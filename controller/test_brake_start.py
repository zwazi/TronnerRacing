import asyncio
import dataclasses
import unittest
from pathlib import Path

from TronnerRacing import (
    DEFAULT_START_COUNTDOWN_SECONDS,
    DEFAULT_START_RESPAWN_DELAY_SECONDS,
    MapEntry,
    MAX_START_RESPAWN_DELAY_SECONDS,
    Player,
    SpawnPoint,
    START_PREFERENCES_STORAGE_KEY,
    TronnerRacing,
    normalize_start_preference,
    plain_console_text,
    start_preference_details,
)


class Sink:
    def __init__(self):
        self.commands = []

    async def send(self, *commands):
        self.commands.extend(commands)


class Store:
    def __init__(self):
        self.values = {}

    def set_json(self, key, value):
        self.values[key] = value


def start_controller(mode="brake"):
    controller = object.__new__(TronnerRacing)
    controller.current = MapEntry(
        "map",
        "Map",
        "Author",
        "v1",
        "maps",
        "map",
        Path("map"),
        (SpawnPoint(3, 4, 0, 1),),
    )
    controller.config = {"go_message_seconds": 30}
    controller.sink = Sink()
    controller.store = Store()
    controller.freeze_tasks = {}
    controller.center_clear_tasks = {}
    controller.spawn_preferences = {}
    controller.start_preferences = {}
    controller.final_countdown_active = False
    controller.transitioning = False
    controller.respawns_paused = False
    player = Player("racer", "Racer", start_mode=mode)
    controller.start_preferences[player.identity_key] = mode
    controller.players = {"racer": player}
    controller.aliases = {"racer": player}
    return controller, player


async def cancel_player_tasks(controller, player):
    tasks = []
    for task_map in (controller.freeze_tasks, controller.center_clear_tasks):
        task = task_map.pop(id(player), None)
        if task:
            task.cancel()
            tasks.append(task)
    if tasks:
        await asyncio.gather(*tasks, return_exceptions=True)


class StartModeTests(unittest.IsolatedAsyncioTestCase):
    def test_engine_uses_stock_brake_protocol_without_decay_override(self):
        root = Path(__file__).resolve().parents[1]
        engine_patch = "\n".join(
            path.read_text(encoding="utf-8")
            for path in (
                root / "engine/patches/tronner-racing.patch",
                root / "engine/patches/start-zone-lifecycle.patch",
            )
        )

        self.assertIn('"RESPAWN_PLAYER_BRAKED"', engine_patch)
        self.assertIn('"RESPAWN_PLAYER_CHECKPOINT_BRAKED"', engine_patch)
        self.assertIn('"RESPAWN_PLAYER_PRACTICE_BRAKED"', engine_patch)
        start_braked = engine_patch.split(
            "+void gCycle::StartBraked(REAL releaseAfterSeconds)", 1
        )[1].split("+void gCycle::RestoreCheckpointState", 1)[0]
        self.assertIn("+    braking = 1;", start_braked)
        self.assertIn("+    startBrakeReleaseSpeed_ = verletSpeed_;", start_braked)
        self.assertNotIn("sg_AcquireClientZeroAcceleration", start_braked)
        self.assertIn("startHoldInitialWinding_", engine_patch)
        self.assertIn("five left on eight axes counts as three turns", engine_patch)
        self.assertIn(
            "if (destination.braking && !freezeBrakeActionDown_)", engine_patch
        )

    def test_private_zone_lifetime_resets_in_place_for_each_cycle(self):
        root = Path(__file__).resolve().parents[1]
        lifecycle_patch = (
            root / "engine/patches/start-zone-lifecycle.patch"
        ).read_text(encoding="utf-8")

        self.assertIn("sg_ResetPrivateZonesForUser(p->Owner())", lifecycle_patch)
        self.assertIn("SetRadius(privateInitialRadius_)", lifecycle_patch)
        self.assertIn(
            "SetExpansionSpeed(privateInitialExpansionSpeed_)", lifecycle_patch
        )
        self.assertIn("RequestSync(privateUser_, true)", lifecycle_patch)
        self.assertNotIn("new gZone", lifecycle_patch)

    async def test_brake_mode_clears_prompt_without_showing_go(self):
        controller, player = start_controller("brake")

        await controller._respawn_player(player)
        await asyncio.sleep(0)

        self.assertIn(
            "RESPAWN_PLAYER_BRAKED racer false 3 4 0 1",
            controller.sink.commands,
        )
        self.assertFalse(
            any(
                command.startswith("RESPAWN_PLAYER_HELD")
                or command.startswith("FREEZE_PLAYER")
                for command in controller.sink.commands
            )
        )
        self.assertIn(
            'CENTER_PLAYER_MESSAGE racer "Press brake to start"',
            [plain_console_text(command) for command in controller.sink.commands],
        )

        await controller._handle_cycle_released("racer 123.456789")

        self.assertEqual(player.attempt_started_game, 123.456789)
        self.assertFalse(player.pending_respawn)
        center_messages = [
            plain_console_text(command)
            for command in controller.sink.commands
            if command.startswith("CENTER_PLAYER_MESSAGE racer")
        ]
        self.assertFalse(any("GO!" in message for message in center_messages))
        self.assertTrue(any(message.endswith('""') for message in center_messages))
        await cancel_player_tasks(controller, player)

    async def test_immediate_mode_uses_unheld_respawn(self):
        controller, player = start_controller("immediate")

        await controller._respawn_player(player)

        self.assertEqual(
            controller.sink.commands,
            ["RESPAWN_PLAYER racer false 3 4 0 1"],
        )
        self.assertNotIn(id(player), controller.freeze_tasks)
        controller._handle_cycle_created("racer 3 4 0 1 50.25")
        self.assertFalse(player.pending_respawn)
        self.assertEqual(player.attempt_started_game, 50.25)
        self.assertEqual(player.attempt_number, 1)

    async def test_release_uses_authoritative_physical_clock_origin(self):
        controller, player = start_controller("brake")

        await controller._respawn_player(player)
        await asyncio.sleep(0)
        await controller._handle_cycle_released("racer 123.75")

        self.assertEqual(player.attempt_started_game, 123.75)
        self.assertFalse(player.pending_respawn)
        await cancel_player_tasks(controller, player)

    async def test_countdown_mode_uses_exact_timed_hold_and_go_cue(self):
        controller, player = start_controller("countdown")

        await controller._respawn_player(player)
        await asyncio.sleep(0)

        self.assertIn(
            "RESPAWN_PLAYER_BRAKED racer false 3 4 0 1 3",
            controller.sink.commands,
        )
        self.assertFalse(
            any(command.startswith("FREEZE_PLAYER") for command in controller.sink.commands)
        )
        self.assertIn(
            'CENTER_PLAYER_MESSAGE racer "3"',
            [plain_console_text(command) for command in controller.sink.commands],
        )

        await controller._handle_cycle_released("racer 53.25")

        self.assertIn(
            'CENTER_PLAYER_MESSAGE racer "     GO!     "',
            [plain_console_text(command) for command in controller.sink.commands],
        )
        await cancel_player_tasks(controller, player)

    async def test_countdown_shares_the_center_with_checkpoint_progress(self):
        controller, player = start_controller("countdown")
        controller.current = dataclasses.replace(
            controller.current, checkpoint_ids=(1, 2, 3)
        )
        player.checkpoints_collected = {1}

        await controller._respawn_player(player)
        await asyncio.sleep(0)

        self.assertIn(
            'CENTER_PLAYER_MESSAGE racer "3                                  0/3"',
            controller.sink.commands,
        )
        self.assertNotIn('CENTER_PLAYER_MESSAGE racer "3"', controller.sink.commands)
        await cancel_player_tasks(controller, player)

    async def test_custom_delay_keeps_fixed_countdown_and_delays_respawn(self):
        controller, player = start_controller("brake")

        await controller._command_start(player, "countdown 7")
        await controller._respawn_player(player)
        await asyncio.sleep(0)

        self.assertEqual(player.start_mode, "countdown")
        self.assertEqual(player.start_respawn_delay_seconds, 7)
        self.assertEqual(
            controller.start_preferences[player.identity_key],
            "countdown 7",
        )
        self.assertEqual(
            controller.store.values[START_PREFERENCES_STORAGE_KEY],
            {player.identity_key: "countdown 7"},
        )
        self.assertIn(
            "RESPAWN_PLAYER_BRAKED racer false 3 4 0 1 3",
            controller.sink.commands,
        )
        self.assertIn(
            'CENTER_PLAYER_MESSAGE racer "3"',
            [plain_console_text(command) for command in controller.sink.commands],
        )
        self.assertTrue(
            any(
                "respawn after 7 seconds" in plain_console_text(command)
                for command in controller.sink.commands
            )
        )
        await controller._handle_cycle_released("racer 57.25")
        self.assertEqual(player.attempt_started_game, 57.25)
        self.assertFalse(player.pending_respawn)
        await cancel_player_tasks(controller, player)

    async def test_plain_countdown_keeps_three_second_default(self):
        controller, player = start_controller("brake")

        await controller._command_start(player, "countdown")

        self.assertEqual(
            player.start_respawn_delay_seconds,
            DEFAULT_START_RESPAWN_DELAY_SECONDS,
        )
        self.assertEqual(
            controller.start_preferences[player.identity_key],
            "countdown",
        )

    async def test_start_rejects_invalid_respawn_seconds_without_changing_mode(self):
        invalid = (
            "countdown 61",
            "countdown -1",
            "countdown nan",
            "countdown 5 extra",
        )
        for argument in invalid:
            with self.subTest(argument=argument):
                controller, player = start_controller("brake")

                await controller._command_start(player, argument)

                self.assertEqual(player.start_mode, "brake")
                self.assertEqual(
                    controller.start_preferences[player.identity_key],
                    "brake",
                )
                self.assertTrue(
                    any(
                        "between 0 and 60" in plain_console_text(command)
                        for command in controller.sink.commands
                    )
                )

    async def test_start_command_persists_preference(self):
        controller, player = start_controller("brake")

        await controller._command_start(player, "countdown")

        self.assertEqual(player.start_mode, "countdown")
        self.assertEqual(controller.start_preferences[player.identity_key], "countdown")
        self.assertEqual(
            controller.store.values[START_PREFERENCES_STORAGE_KEY],
            {player.identity_key: "countdown"},
        )
        self.assertTrue(
            any(
                "Start mode set to countdown" in plain_console_text(command)
                for command in controller.sink.commands
            )
        )

    def test_new_player_defaults_to_immediate(self):
        self.assertEqual(Player("racer", "Racer").start_mode, "immediate")

    def test_start_preference_parser_accepts_delay_for_every_mode(self):
        self.assertEqual(normalize_start_preference("countdown"), "countdown")
        self.assertEqual(normalize_start_preference("countdown 0"), "countdown")
        self.assertEqual(normalize_start_preference("brake 1.5"), "brake 1.5")
        self.assertEqual(
            normalize_start_preference(
                f"immediate {MAX_START_RESPAWN_DELAY_SECONDS:g}"
            ),
            f"immediate {MAX_START_RESPAWN_DELAY_SECONDS:g}",
        )
        self.assertIsNone(normalize_start_preference("countdown -1"))
        self.assertEqual(
            start_preference_details("countdown 12"),
            ("countdown", 12.0, "countdown 12"),
        )


if __name__ == "__main__":
    unittest.main()
