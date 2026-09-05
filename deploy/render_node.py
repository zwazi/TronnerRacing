#!/usr/bin/env python3
"""Render the standalone Tronner Racing service from operator-owned JSON."""

from __future__ import annotations

import argparse
import ipaddress
import json
import os
import re
import sys
import tempfile
import urllib.parse
from pathlib import Path
from typing import Any


IDENTIFIER = re.compile(r"^[A-Za-z0-9][A-Za-z0-9._:-]{0,63}$")
REGION_LABEL = re.compile(r"^[A-Za-z0-9][A-Za-z0-9_-]{0,15}$")
GIT_REF = re.compile(r"^[A-Za-z0-9](?:[A-Za-z0-9._/-]{0,126}[A-Za-z0-9])?$")
EXAMPLE_HOST_SUFFIXES = (
    ".example", ".example.com", ".example.net", ".example.org",
    ".example.invalid", ".invalid", ".test",
)


class ConfigurationError(ValueError):
    """Raised when an operator input is unsafe or incomplete."""


def reject_duplicate_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ConfigurationError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def load_object(path: Path) -> dict[str, Any]:
    try:
        value = json.loads(
            path.read_text(encoding="utf-8"),
            object_pairs_hook=reject_duplicate_keys,
        )
    except (OSError, json.JSONDecodeError) as exc:
        raise ConfigurationError(f"unable to read {path}: {exc}") from exc
    if not isinstance(value, dict):
        raise ConfigurationError(f"{path} must contain a JSON object")
    if value.get("schema_version") != 1:
        raise ConfigurationError(f"{path} must use schema_version 1")
    return value


def identifier(value: object, label: str) -> str:
    text = str(value).strip()
    if not IDENTIFIER.fullmatch(text):
        raise ConfigurationError(f"invalid {label}")
    return text


def region_label(value: object) -> str:
    text = str(value).strip()
    if not REGION_LABEL.fullmatch(text):
        raise ConfigurationError("invalid region label")
    return text


def git_ref(value: object) -> str:
    text = str(value).strip()
    if (
        not GIT_REF.fullmatch(text)
        or ".." in text
        or "//" in text
        or text.endswith(".lock")
        or text.startswith("-")
    ):
        raise ConfigurationError("invalid repository branch")
    return text


def bounded_line(value: object, label: str, maximum: int = 256) -> str:
    text = str(value).strip()
    if not text or len(text) > maximum or any(ch in text for ch in "\r\n\0"):
        raise ConfigurationError(f"invalid {label}")
    return text


def port(value: object, label: str) -> int:
    if isinstance(value, bool):
        raise ConfigurationError(f"invalid {label}")
    try:
        number = int(value)
    except (TypeError, ValueError) as exc:
        raise ConfigurationError(f"invalid {label}") from exc
    if not 1 <= number <= 65535:
        raise ConfigurationError(f"invalid {label}")
    return number


def literal_ip(value: object, label: str) -> str:
    try:
        return str(ipaddress.ip_address(str(value).strip()))
    except ValueError as exc:
        raise ConfigurationError(f"{label} must be a literal IP address") from exc


def url(value: object, label: str, *, allow_http: bool) -> str:
    text = bounded_line(value, label, 512)
    parsed = urllib.parse.urlsplit(text)
    allowed = {"https"} | ({"http"} if allow_http else set())
    if (
        parsed.scheme not in allowed
        or not parsed.hostname
        or parsed.username
        or parsed.password
        or parsed.query
        or parsed.fragment
    ):
        raise ConfigurationError(f"invalid {label}")
    return text


def example_hostname(hostname: str) -> bool:
    lowered = hostname.casefold().rstrip(".")
    return lowered in {
        "example.com", "example.net", "example.org", "localhost", "test"
    } or lowered.endswith(EXAMPLE_HOST_SUFFIXES)


def atomic_write(path: Path, data: str, mode: int = 0o640) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, name = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    temporary = Path(name)
    try:
        with os.fdopen(descriptor, "w", encoding="utf-8", newline="\n") as output:
            output.write(data)
            output.flush()
            os.fsync(output.fileno())
        os.chmod(temporary, mode)
        temporary.replace(path)
    finally:
        temporary.unlink(missing_ok=True)


def json_text(value: object) -> str:
    return json.dumps(value, indent=2, sort_keys=True) + "\n"


def render(cluster: dict[str, Any], node: dict[str, Any], *, production: bool) -> dict[str, str]:
    service_id = identifier(cluster.get("service_id", ""), "service ID")
    server_id = identifier(node.get("server_id", ""), "server ID")
    region = region_label(node.get("region_label", ""))
    if str(node.get("role", "standalone")).strip().casefold() != "standalone":
        raise ConfigurationError("Tronner Racing supports only a standalone server")

    server_name = bounded_line(node.get("server_name", ""), "server name")
    website_url = url(node.get("website_url", ""), "website URL", allow_http=False)
    public_base_url = url(
        node.get("public_base_url", ""), "public map base URL", allow_http=True
    )
    if not public_base_url.endswith("/"):
        public_base_url += "/"
    server_dns = str(node.get("server_dns", "")).strip()
    if server_dns:
        server_dns = bounded_line(server_dns, "server DNS name", 253)
        if any(ch in server_dns for ch in " /:@"):
            raise ConfigurationError("invalid server DNS name")
    game_bind = literal_ip(node.get("game_bind", "0.0.0.0"), "game bind")
    game_port = port(node.get("game_port", 4534), "game port")
    resource_bind = literal_ip(
        node.get("resource_bind", "0.0.0.0"), "resource bind"
    )
    resource_port = port(node.get("resource_port", 8080), "resource port")
    master_list = node.get("master_list", False)
    if not isinstance(master_list, bool):
        raise ConfigurationError("master_list must be true or false")

    maps = cluster.get("map_repository")
    if not isinstance(maps, dict):
        raise ConfigurationError("map_repository must be an object")
    repository_source = str(maps.get("source", "git")).strip().casefold()
    if repository_source not in {"git", "firebase"}:
        raise ConfigurationError("map_repository source must be git or firebase")
    repository_url = url(
        maps.get("url", ""), "map repository URL", allow_http=False
    )
    repository_branch = git_ref(maps.get("branch", "main"))

    firebase = cluster.get("firebase", {})
    if not isinstance(firebase, dict) or not isinstance(
        firebase.get("enabled", False), bool
    ):
        raise ConfigurationError("firebase must contain a boolean enabled flag")
    firebase_enabled = firebase.get("enabled", False)
    if repository_source == "firebase" and not firebase_enabled:
        raise ConfigurationError("Firebase map catalogs require firebase.enabled")

    controller: dict[str, Any] = {
        "server_id": server_id,
        "repository_source": repository_source,
        "repository_git_url": repository_url,
        "repository_branch": repository_branch,
        "repository_checkout": "/var/lib/tronner-racing/repository",
        # Firebase uses its version document as a background invalidation signal.
        # Startup should use the already-validated immutable local snapshot.
        "repository_auto_sync": repository_source != "firebase",
        "repository_refresh_seconds": 300,
        "public_dir": "/var/lib/tronner-racing/public",
        "public_bind": resource_bind,
        "public_port": resource_port,
        "public_base_url": public_base_url,
        "resource_cache_dir": "/var/lib/armagetronad/resource/automatic",
        "map_override_dir": "/var/lib/tronner-racing/map-overrides",
        "map_revision_dir": "/var/lib/tronner-racing/map-revisions",
        "dtd_source_dir": "/opt/armagetronad/share/games/armagetronad-dedicated/resource/included",
        "console_input": "/var/lib/armagetronad/console.in",
        "ladderlog": "/var/lib/armagetronad/ladderlog.txt",
        "online_players_file": "/var/lib/armagetronad/online_players.txt",
        "database": "/var/lib/tronner-racing/TronnerRacing.sqlite3",
        "ghost_plan_dir": "/var/lib/armagetronad/ghosts",
        "spawn_preferences_file": "/var/lib/tronner-racing/spawn_preferences.json",
        "helpful_messages_file": "/etc/tronner-racing/helpful_messages.txt",
        "map_duration_seconds": 300,
        "minimum_map_duration_seconds": 120,
        "map_time_racer_multiplier": 1.25,
        "map_time_target_finishes": 5,
        "extend_seconds": 300,
        "freeze_seconds": 3.0,
        "freeze_tick_seconds": 0.05,
        "respawn_delay_seconds": 2.0,
        "checkpoint_respawn_delay_seconds": 0.1,
        "checkpoint_double_respawn_seconds": 1.5,
        "practice_probe_interval_seconds": 0.25,
        "practice_max_rewind_seconds": 300,
        "practice_deathzone_protection_enabled": True,
        "go_message_seconds": 1.0,
        "final_countdown_idle_seconds": 10,
        "final_countdown_progress_guard_enabled": True,
        "final_countdown_progress_wrong_way_allowance_seconds": 5.0,
        "final_countdown_progress_warning_delay_seconds": 1.0,
        "final_countdown_progress_direction_slack_distance": 0.25,
        "final_countdown_progress_max_sample_gap_seconds": 2.0,
        "final_countdown_progress_stationary_limit_seconds": 5.0,
        "final_countdown_progress_stationary_warning_delay_seconds": 1.0,
        "final_countdown_progress_stationary_position_epsilon": 0.01,
        "final_countdown_progress_same_turn_limit": 15,
        "final_countdown_progress_probe_interval_seconds": 1.0,
        "final_countdown_route_maximum_cells": 250_000,
        "final_countdown_route_minimum_cell_size": 0.5,
        "final_countdown_route_retry_maximum_cells": 500_000,
        "final_countdown_route_retry_minimum_cell_size": 0.1,
        "final_countdown_route_cache_dir": "/var/lib/tronner-racing/route-fields",
        "final_countdown_route_cache_maximum_entries": 768,
        "final_countdown_route_cache_maximum_bytes": 512 * 1024 * 1024,
        "clock_runout_prevention_enabled": True,
        "clock_runout_minimum_seconds": 120,
        "clock_runout_personal_best_multiplier": 3,
        "clock_runout_checkpoint_grace_seconds": 20,
        "afk_timeout_seconds": 60,
        "round_display_delay_seconds": 0.35,
        "round_intermission_display_delay_seconds": 0.0,
        "map_transition_timeout_seconds": 20,
        "map_transition_probe_seconds": 1,
        "map_transition_failure_confirmations": 2,
        "command_rate_maximum": 4,
        "command_rate_window_seconds": 5,
        "command_rate_warning_interval_seconds": 5,
        "maximum_record_seconds": 7200,
        "default_size_factor": 0,
        "size_admin_access_level": 1,
        "map_admin_access_level": 1,
        "records_admin_access_level": 1,
        "firebase_catalog_dir": "/var/lib/tronner-racing/firebase-catalog",
        "firebase_catalog_require_ready": True,
        "firebase_request_timeout_seconds": 20,
        "firebase_server_id": server_id,
        "live_dashboard": {
            "enabled": False,
            "chat_enabled": False,
            "management_enabled": False,
            "local_region": region,
        },
    }

    database_url = ""
    if firebase_enabled:
        controller.update({
            "firebase_project_id": identifier(
                firebase.get("project_id", ""), "Firebase project ID"
            ),
            "firebase_storage_bucket": bounded_line(
                firebase.get("storage_bucket", ""), "Firebase bucket"
            ),
            "firebase_service_account_file": "/etc/tronner-racing/firebase-service-account.json",
        })
        live_enabled = firebase.get("live_dashboard_enabled", False)
        management_enabled = firebase.get("management_enabled", False)
        if not isinstance(live_enabled, bool) or not isinstance(management_enabled, bool):
            raise ConfigurationError("Firebase feature flags must be true or false")
        if live_enabled:
            database_url = url(
                firebase.get("database_url", ""),
                "Firebase database URL",
                allow_http=False,
            )
            controller["live_dashboard"] = {
                "enabled": True,
                "chat_enabled": True,
                "management_enabled": management_enabled,
                "database_url": database_url,
                "local_region": region,
            }

    if production:
        hostnames = [
            urllib.parse.urlsplit(website_url).hostname or "",
            urllib.parse.urlsplit(public_base_url).hostname or "",
            urllib.parse.urlsplit(repository_url).hostname or "",
        ]
        if service_id.casefold().startswith("example-"):
            raise ConfigurationError("replace the example service ID")
        if any(example_hostname(hostname) for hostname in hostnames):
            raise ConfigurationError("replace example hostnames")
        if server_name.casefold().startswith("example "):
            raise ConfigurationError("replace the example server name")
        if server_dns and example_hostname(server_dns):
            raise ConfigurationError("replace the example server DNS name")
        if database_url and example_hostname(
            urllib.parse.urlsplit(database_url).hostname or ""
        ):
            raise ConfigurationError("replace the example Firebase database URL")

    server_lines = [
        "# Generated by deploy/render_node.py. Do not edit on the server.",
        f"SERVER_PORT {game_port}",
        f"SERVER_IP {game_bind}",
        f"TALK_TO_MASTER {1 if master_list else 0}",
        f"SERVER_NAME {server_name}",
        f"URL {website_url}",
        f"RESOURCE_REPOSITORY_SERVER {public_base_url}",
    ]
    if server_dns:
        server_lines.append(f"SERVER_DNS {server_dns}")
    server_lines.extend(["GLOBAL_ID 1", "INCLUDE tronner-racing.cfg", ""])

    manifest = {
        "schemaVersion": 1,
        "serviceId": service_id,
        "serverId": server_id,
        "role": "standalone",
        "masterListEnabled": master_list,
        "firebaseEnabled": firebase_enabled,
        "requiredSecretFiles": [],
    }
    return {
        "controller.json": json_text(controller),
        "server.cfg": "\n".join(server_lines),
        "manifest.json": json_text(manifest),
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cluster", type=Path, required=True)
    parser.add_argument("--node", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--production", action="store_true")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    try:
        cluster = load_object(args.cluster)
        node = load_object(args.node)
        rendered = render(cluster, node, production=args.production)
        args.output.mkdir(parents=True, exist_ok=True)
        os.chmod(args.output, 0o750)
        for name, contents in rendered.items():
            atomic_write(args.output / name, contents)
    except ConfigurationError as exc:
        print(f"configuration error: {exc}", file=sys.stderr)
        return 2
    print(f"rendered {len(rendered)} files for {node['server_id']} in {args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
