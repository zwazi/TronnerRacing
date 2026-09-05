import tempfile
import unittest
from pathlib import Path

from TronnerRacing import (
    CheckpointEntry,
    CheckpointSnapshot,
    MapEntry,
    MapRepository,
    Player,
    Record,
    SpawnPoint,
    StateStore,
    TronnerRacing,
    parse_checkpoint_entry,
)


CHECKPOINT_MAP = b'''<Resource type="aamap" name="Checkpoints" version="1" author="Tester" category="maps">
<Map version="0.2.8"><Settings>
<Setting name="RACE_CHECKPOINT_REQUIRE_HIT" value="{mode}" />
</Settings><World><Field><Spawn x="0" y="0" xdir="1" ydir="0"/>
<Zone effect="checkpoint"><ShapeCircle radius="5"><Point x="10" y="0"/><Checkpoint id="2" time="99"/></ShapeCircle></Zone>
<Zone effect="checkpoint"><ShapeCircle radius="5"><Point x="20" y="0"/><Checkpoint id="1" time="0"/></ShapeCircle></Zone>
<Zone effect="checkpoint"><ShapeCircle radius="5"><Point x="20" y="5"/><Checkpoint id="1" time="0"/></ShapeCircle></Zone>
</Field></World></Map></Resource>'''


class Sink:
    def __init__(self):
        self.commands = []

    async def send(self, *commands):
        self.commands.extend(commands)


def checkpoint_controller(mode="ordered"):
    controller = object.__new__(TronnerRacing)
    controller.current = MapEntry(
        "map", "Map", "Author", "1", "maps", "map", Path("map"),
        (SpawnPoint(0, 0, 1, 0),), checkpoint_ids=(1, 2),
        checkpoint_mode=mode,
    )
    controller.config = {"maximum_record_seconds": 7200}
    controller.sink = Sink()
    controller.finalists = set()
    controller.finishes_in_progress = set()
    controller.final_countdown_active = False
    player = Player("racer", "Racer", alive=True, attempt_started_game=10.0)
    controller.players = {"racer": player}
    controller.aliases = {"racer": player}
    messages = []

    async def private(_player, message):
        messages.append(message)

    controller.private = private
    return controller, player, messages


class CheckpointMapTests(unittest.TestCase):
    def parse(self, mode):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            checkout = root / "catalog"
            checkout.mkdir()
            source = checkout / "map.aamap.xml"
            source.write_bytes(CHECKPOINT_MAP.replace(b"{mode}", str(mode).encode()))
            repository = MapRepository({
                "repository_git_url": "unused",
                "repository_checkout": str(checkout),
                "public_dir": str(root / "public"),
                "resource_cache_dir": str(root / "cache"),
                "dtd_source_dir": str(root / "dtd"),
                "map_override_dir": str(root / "overrides"),
                "map_revision_dir": str(root / "revisions"),
            })
            repository.scan()
            return next(iter(repository.catalog.values()))

    def test_map_mode_and_unique_checkpoint_ids_are_parsed(self):
        ordered = self.parse(2)
        unordered = self.parse(1)
        self.assertEqual(ordered.checkpoint_ids, (1, 2))
        self.assertEqual(ordered.checkpoint_mode, "ordered")
        self.assertEqual(unordered.checkpoint_mode, "unordered")

    def test_checkpoint_event_parser(self):
        self.assertEqual(
            parse_checkpoint_entry("racer 3 12.5"),
            CheckpointEntry("racer", 3, 12.5),
        )
        self.assertEqual(
            parse_checkpoint_entry("racer 3 10 20 0 1 12.5 7 15.25"),
            CheckpointEntry(
                "racer", 3, 15.25, 10.0, 20.0, 0.0, 1.0, 12.5, 7
            ),
        )
        self.assertIsNone(parse_checkpoint_entry("racer nope 12.5"))
        self.assertIsNone(
            parse_checkpoint_entry("racer 3 10 20 0 0 12.5 7 15.25")
        )


class CheckpointEnforcementTests(unittest.IsolatedAsyncioTestCase):
    async def test_ordered_map_rejects_out_of_order_checkpoint(self):
        controller, player, messages = checkpoint_controller("ordered")

        await controller._handle_checkpoint("racer 2 11")
        self.assertEqual(player.checkpoints_collected, set())
        self.assertIn("Checkpoint 1 must be collected next.", messages)

        player.checkpoint_notice_monotonic = None
        await controller._handle_checkpoint("racer 1 12")
        await controller._handle_checkpoint("racer 2 13")
        self.assertEqual(player.checkpoints_collected, {1, 2})
        self.assertEqual(messages, ["Checkpoint 1 must be collected next."])
        self.assertIsNone(player.checkpoint_snapshot)
        self.assertIn(
            "SET_CHECKPOINT_PLAYER_COLOR racer 2",
            controller.sink.commands,
        )
        self.assertIn(
            'CENTER_PLAYER_MESSAGE racer "0xffffff                                  2/2"',
            controller.sink.commands,
        )

    async def test_unordered_map_accepts_any_order(self):
        controller, player, _messages = checkpoint_controller("unordered")

        await controller._handle_checkpoint("racer 2 11")
        await controller._handle_checkpoint("racer 1 12")
        self.assertEqual(player.checkpoints_collected, {1, 2})

    async def test_latest_checkpoint_remains_available_until_finish(self):
        controller, player, messages = checkpoint_controller("unordered")
        player.no_cp_segment_started_game = 10.0

        await controller._handle_checkpoint(
            "racer 1 10 20 0 1 12.5 7 14.25"
        )
        self.assertIsNotNone(player.checkpoint_snapshot)

        await controller._handle_checkpoint(
            "racer 2 20 30 1 0 14 9 18.5"
        )

        self.assertEqual(player.checkpoints_collected, {1, 2})
        self.assertIsNotNone(player.checkpoint_snapshot)
        self.assertEqual(player.checkpoint_snapshot.checkpoint_id, 2)
        self.assertNotIn("No checkpoint is available for this run yet.", messages)

    async def test_normal_spawn_resets_private_checkpoint_colors(self):
        controller, player, _messages = checkpoint_controller("unordered")
        controller.freeze_tasks = {}
        controller.center_clear_tasks = {}
        controller.spawn_preferences = {}
        controller.start_preferences = {player.identity_key: "immediate"}
        controller.final_countdown_active = False
        controller.transitioning = False
        controller.respawns_paused = False
        player.start_mode = "immediate"
        player.connected = True
        player.active = True
        player.respawn_enabled = True
        player.alive = False

        await controller._respawn_player(player)

        self.assertEqual(
            controller.sink.commands[-2:],
            [
                "RESET_CHECKPOINT_PLAYER_COLORS racer",
                "RESPAWN_PLAYER racer false 0 0 1 0",
            ],
        )

    async def test_checkpoint_snapshot_captures_motion_and_successful_time(self):
        controller, player, _messages = checkpoint_controller("ordered")
        player.no_cp_segment_started_game = 10.0

        await controller._handle_checkpoint(
            "racer 1 10 20 0 1 12.5 7 14.25"
        )

        self.assertEqual(
            player.checkpoint_snapshot,
            CheckpointSnapshot(
                checkpoint_id=1,
                x=10.0,
                y=20.0,
                xdir=0.0,
                ydir=1.0,
                speed=12.5,
                turns=7,
                event_game=14.25,
                attempt_started_game=10.0,
                checkpoints_collected=frozenset({1}),
                no_cp_elapsed=4.25,
            ),
        )
        self.assertEqual(player.no_cp_segment_started_game, 14.25)

    async def test_checkpoint_events_are_ignored_during_start_hold(self):
        controller, player, _messages = checkpoint_controller("ordered")
        player.pending_respawn = True
        player.pending_respawn_kind = "checkpoint"

        await controller._handle_checkpoint(
            "racer 1 10 20 0 1 12.5 7 14.25"
        )

        self.assertEqual(player.checkpoints_collected, set())
        self.assertIsNone(player.checkpoint_snapshot)

    async def test_finish_is_blocked_without_killing_the_run(self):
        controller, player, messages = checkpoint_controller("ordered")

        await controller._handle_winzone("1 finish 0 0 racer 5 5 1 0 turns=4 20")

        self.assertTrue(player.alive)
        self.assertEqual(player.attempt_started_game, 10.0)
        self.assertFalse(controller.sink.commands)
        self.assertIn("Finish blocked: collect checkpoint 1 next (0/2).", messages)

    async def test_winzone_ignores_held_spawn_before_takeoff(self):
        controller, player, messages = checkpoint_controller("unordered")
        player.pending_respawn = True
        player.pending_respawn_kind = "spawn"
        player.attempt_started_game = None

        for game_time in (20.0, 20.01, 20.02):
            await controller._handle_winzone(
                f"1 finish 0 0 racer 0 0 0 1 turns=0 {game_time}"
            )

        self.assertTrue(player.alive)
        self.assertTrue(player.pending_respawn)
        self.assertEqual(controller.sink.commands, [])
        self.assertEqual(messages, [])

    async def test_successful_finish_clears_progress_and_private_colors(self):
        controller, player, _messages = checkpoint_controller("unordered")
        player.checkpoints_collected = {1, 2}
        with tempfile.TemporaryDirectory() as tmp:
            controller.store = StateStore(Path(tmp) / "state.sqlite3")

            await controller._handle_winzone(
                "1 finish 0 0 racer 5 5 1 0 turns=4 20"
            )

            self.assertEqual(player.checkpoints_collected, set())
            self.assertIsNone(player.checkpoint_snapshot)
            reset_index = controller.sink.commands.index(
                "RESET_CHECKPOINT_PLAYER_COLORS racer"
            )
            score_index = controller.sink.commands.index(
                "ADD_SCORE_PLAYER racer 1"
            )
            self.assertLess(reset_index, score_index)
            controller.store.close()

    async def test_delayed_old_cycle_destroy_keeps_replacement_progress(self):
        controller, player, _messages = checkpoint_controller("ordered")
        player.pending_respawn = True
        player.respawn_created_game = None
        player.checkpoints_collected = {1}

        await controller._handle_cycle_destroyed("racer")

        self.assertEqual(player.checkpoints_collected, {1})


if __name__ == "__main__":
    unittest.main()
