import json
import tempfile
import unittest
from pathlib import Path

import render_node


ROOT = Path(__file__).resolve().parents[1]


class RenderTests(unittest.TestCase):
    def load(self, name):
        return render_node.load_object(ROOT / "config" / name)

    def test_standalone_example_is_inert(self):
        rendered = render_node.render(
            self.load("cluster.example.json"),
            self.load("node.example.json"),
            production=False,
        )
        manifest = json.loads(rendered["manifest.json"])
        self.assertEqual(manifest["role"], "standalone")
        self.assertFalse(manifest["masterListEnabled"])
        self.assertFalse(manifest["firebaseEnabled"])
        self.assertEqual(
            set(rendered), {"controller.json", "server.cfg", "manifest.json"}
        )
        self.assertIn("TALK_TO_MASTER 0", rendered["server.cfg"])
        self.assertEqual(
            json.loads(rendered["controller.json"])["ghost_plan_dir"],
            "/var/lib/armagetronad/ghosts",
        )

    def test_non_standalone_role_is_rejected(self):
        node = self.load("node.example.json")
        node["role"] = "peer"
        with self.assertRaisesRegex(
            render_node.ConfigurationError, "only a standalone server"
        ):
            render_node.render(
                self.load("cluster.example.json"), node, production=False
            )

    def test_production_mode_rejects_examples(self):
        with self.assertRaises(render_node.ConfigurationError):
            render_node.render(
                self.load("cluster.example.json"),
                self.load("node.example.json"),
                production=True,
            )

    def test_production_standalone_retains_firebase_integrations(self):
        cluster = self.load("cluster.example.json")
        cluster.update(
            {
                "service_id": "tronner-racing",
                "map_repository": {
                    "source": "firebase",
                    "url": "https://github.com/zwazi/TronnerRepository.git",
                    "branch": "main",
                },
                "firebase": {
                    "enabled": True,
                    "project_id": "tronner-racing",
                    "storage_bucket": "tronner-racing.appspot.com",
                    "database_url": (
                        "https://tronner-racing-default-rtdb." + "firebaseio.com"
                    ),
                    "catalog_enabled": True,
                    "live_dashboard_enabled": True,
                    "management_enabled": True,
                },
            }
        )
        node = self.load("node.example.json")
        node.update(
            {
                "server_id": "nyc1",
                "region_label": "NY",
                "server_name": "Tronner Racing",
                "website_url": "https://tronner.io/",
                "server_dns": "race.tronner.io",
                "public_base_url": "http://maps.tronner.io:8080/",
                "master_list": True,
            }
        )

        rendered = render_node.render(cluster, node, production=True)
        manifest = json.loads(rendered["manifest.json"])
        controller = json.loads(rendered["controller.json"])
        self.assertTrue(manifest["firebaseEnabled"])
        self.assertTrue(manifest["masterListEnabled"])
        self.assertEqual(manifest["role"], "standalone")
        self.assertEqual(controller["server_id"], "nyc1")
        self.assertTrue(controller["live_dashboard"]["enabled"])
        self.assertTrue(controller["live_dashboard"]["management_enabled"])

    def test_duplicate_json_keys_are_rejected(self):
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "duplicate.json"
            path.write_text(
                '{"schema_version":1,"schema_version":1}', encoding="utf-8"
            )
            with self.assertRaises(render_node.ConfigurationError):
                render_node.load_object(path)

    def test_safe_nested_git_branch_is_accepted(self):
        cluster = self.load("cluster.example.json")
        cluster["map_repository"]["branch"] = "release/2026-08"
        rendered = render_node.render(
            cluster, self.load("node.example.json"), production=False
        )
        self.assertEqual(
            json.loads(rendered["controller.json"])["repository_branch"],
            "release/2026-08",
        )

    def test_unsafe_git_branch_is_rejected(self):
        cluster = self.load("cluster.example.json")
        for branch in ("../main", "main..other", "main.lock", "-main"):
            with self.subTest(branch=branch):
                cluster["map_repository"]["branch"] = branch
                with self.assertRaises(render_node.ConfigurationError):
                    render_node.render(
                        cluster, self.load("node.example.json"), production=False
                    )


if __name__ == "__main__":
    unittest.main()
