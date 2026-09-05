import asyncio
import unittest
from pathlib import Path
from unittest.mock import Mock

from TronnerRacing import MapEntry, Player, SpawnPoint, TronnerRacing, plain_console_text


class Sink:
    def __init__(self):
        self.commands = []

    async def send(self, *commands):
        self.commands.extend(commands)


def practice_controller(start_mode="immediate"):
    controller = object.__new__(TronnerRacing)
    controller.current = MapEntry(
        "Author/maps/Practice-v1.aamap.xml",
        "Practice",
        "Author",
        "1",
        "maps",
        "Practice-v1.aamap.xml",
        Path("Practice-v1.aamap.xml"),
        (SpawnPoint(3, 4, 0, 1),),
        axes=4,
    )
    controller.current_size_factor = 0
    controller.config = {
        "practice_max_rewind_seconds": 300,
        "practice_probe_interval_seconds": 0.25,
        "respawn_delay_seconds": 0,
        "empty_arena_respawn_delay_seconds": 0,
        "go_message_seconds": 30,
    }
    controller.sink = Sink()
    controller.round_active = True
    controller.transitioning = False
    controller.final_countdown_active = False
    controller.server_restart_active = False
    controller.respawns_paused = False
    controller.last_game_time = 0.0
    controller.last_game_monotonic = None
    controller.next_activity_probe_monotonic = 99.0
    controller.respawn_tasks = {}
    controller.freeze_tasks = {}
    controller.center_clear_tasks = {}
    controller.spawn_preferences = {}
    controller.start_preferences = {}
    controller.finalists = set()
    controller.replay_captures = {}
    controller.active_replay_tokens = {}
    player = Player(
        "racer",
        "Racer",
        connected=True,
        active=True,
        alive=True,
        start_mode=start_mode,
    )
    controller.start_preferences[player.identity_key] = (
        "countdown 7" if start_mode == "countdown" else start_mode
    )
    controller.players = {"racer": player}
    controller.aliases = {"racer": player}
    return controller, player


async def cancel_tasks(controller):
    tasks = []
    for mapping in (
        controller.respawn_tasks,
        controller.freeze_tasks,
        controller.center_clear_tasks,
    ):
        tasks.extend(mapping.values())
        mapping.clear()
    for task in tasks:
        task.cancel()
    if tasks:
        await asyncio.gather(*tasks, return_exceptions=True)


class PracticeModeTests(unittest.IsolatedAsyncioTestCase):
    async def test_command_enables_map_scoped_mode_and_off_clears_it(self):
        controller, player = practice_controller()

        await controller._command_practice(player, "maintain 2.5")

        self.assertEqual(player.practice_mode, "maintain")
        self.assertEqual(player.practice_rewind_seconds, 2.5)
        self.assertEqual(player.practice_map_key, controller.current.key)
        self.assertTrue(player.practice_attempt_tainted)
        self.assertEqual(controller.next_activity_probe_monotonic, 0.0)
        self.assertIn("GET_PLAYER_ACTIVITY", controller.sink.commands)
        self.assertTrue(
            any(
                "finishes do not record a time" in plain_console_text(command)
                for command in controller.sink.commands
            )
        )

        await controller._command_practice(player, "off")

        self.assertFalse(controller._practice_active(player))
        self.assertEqual(player.practice_mode, "off")
        self.assertFalse(player.practice_samples)
        self.assertTrue(player.practice_attempt_tainted)

    async def test_disabling_mid_life_cannot_make_that_finish_score(self):
        controller, player = practice_controller()
        controller.store = Mock()
        player.attempt_started_game = 1.0

        await controller._command_practice(player, "reset 0")
        await controller._command_practice(player, "off")
        await controller._handle_winzone(
            "1 finish 0 0 racer 0 0 1 0 12.5"
        )

        self.assertFalse(controller._practice_active(player))
        self.assertTrue(player.practice_attempt_tainted)
        self.assertIn("KILL_SILENT racer", controller.sink.commands)
        self.assertFalse(
            any(
                command.startswith("ADD_SCORE_PLAYER")
                for command in controller.sink.commands
            )
        )
        controller.store.add_finish.assert_not_called()

    async def test_countdown_disables_practice_but_taints_current_life(self):
        controller, player = practice_controller()
        player.practice_mode = "maintain"
        player.practice_map_key = controller.current.key
        player.practice_attempt_tainted = True

        await controller._disable_practice_for_countdown()

        self.assertFalse(controller._practice_active(player))
        self.assertTrue(player.practice_attempt_tainted)
        self.assertTrue(
            any(
                "disabled for the countdown" in plain_console_text(command)
                for command in controller.sink.commands
            )
        )

    async def test_command_rejects_invalid_modes_and_unbounded_rewinds(self):
        controller, player = practice_controller()

        for argument in ("reset", "unknown 2", "maintain -1", "reset 301"):
            with self.subTest(argument=argument):
                controller.sink.commands.clear()
                await controller._command_practice(player, argument)
                self.assertEqual(player.practice_mode, "off")
                self.assertTrue(
                    any(
                        "Usage:" in plain_console_text(command)
                        or "from 0 to 300" in plain_console_text(command)
                        for command in controller.sink.commands
                    )
                )

    async def test_zero_seconds_uses_exact_death_position_and_reset_speed(self):
        controller, player = practice_controller()
        player.practice_mode = "reset"
        player.practice_map_key = controller.current.key
        player.practice_rewind_seconds = 0
        scheduled = []
        controller._schedule_respawn = (
            lambda candidate, delay_seconds=None: scheduled.append(
                (candidate, delay_seconds)
            )
        )

        await controller._handle_cycle_destroyed(
            "racer 91.25 -17.5 0 -1 obstacle 22.75 DEATHZONE"
        )

        snapshot = player.practice_respawn_snapshot
        self.assertIsNotNone(snapshot)
        self.assertEqual((snapshot.x, snapshot.y), (91.25, -17.5))
        self.assertEqual((snapshot.xdir, snapshot.ydir), (0.0, -1.0))
        self.assertEqual(scheduled, [(player, 0.0)])

        await controller._respawn_player(player)
        self.assertIn(
            "RESPAWN_PLAYER_CHECKPOINT racer false 91.25 -17.5 0 -1 0 0",
            controller.sink.commands,
        )

    async def test_maintain_rewinds_to_recorded_path_state(self):
        controller, player = practice_controller()
        player.alive = False
        player.practice_mode = "maintain"
        player.practice_map_key = controller.current.key
        player.practice_rewind_seconds = 2
        controller._record_practice_snapshot(
            player, 10, 0, 0, xdir=1, ydir=0, speed=20, turns=1
        )
        controller._record_practice_snapshot(
            player, 11, 20, 0, xdir=1, ydir=0, speed=22, turns=2
        )
        controller._record_practice_snapshot(
            player, 12, 50, 0, xdir=1, ydir=0, speed=30, turns=3
        )

        controller._prepare_practice_respawn(
            player, 13, 90, 0, 1, 0, speed=40, turns=4
        )
        await controller._respawn_player(player)

        self.assertIn(
            "RESPAWN_PLAYER_CHECKPOINT racer false 20 0 1 0 22 2",
            controller.sink.commands,
        )

    async def test_practice_respawn_honors_countdown_start_setting(self):
        controller, player = practice_controller("countdown")
        player.alive = False
        player.practice_mode = "maintain"
        player.practice_map_key = controller.current.key
        controller._prepare_practice_respawn(
            player, 5, 10, 20, 0, 1, speed=31.5, turns=8
        )

        await controller._respawn_player(player)

        self.assertEqual(
            controller.sink.commands,
            [
                "RESPAWN_PLAYER_CHECKPOINT_BRAKED "
                "racer false 10 20 0 1 31.5 8 3",
            ],
        )
        await cancel_tasks(controller)

    async def test_practice_respawn_honors_brake_start_setting(self):
        controller, player = practice_controller("brake")
        player.alive = False
        player.practice_mode = "reset"
        player.practice_map_key = controller.current.key
        controller._prepare_practice_respawn(
            player, 5, 10, 20, 0, 1, speed=31.5, turns=8
        )

        await controller._respawn_player(player)

        self.assertIn(
            "RESPAWN_PLAYER_CHECKPOINT_BRAKED racer false 10 20 0 1 0 8",
            controller.sink.commands,
        )
        self.assertNotIn("FREEZE_PLAYER racer 3", controller.sink.commands)
        await cancel_tasks(controller)

    async def test_native_zone_protection_uses_practice_respawn_commands(self):
        controller, player = practice_controller("countdown")
        controller.config["practice_deathzone_protection_enabled"] = True
        player.alive = False
        player.practice_mode = "maintain"
        player.practice_map_key = controller.current.key
        controller._prepare_practice_respawn(
            player, 5, 10, 20, 0, 1, speed=31.5, turns=8
        )

        await controller._respawn_player(player)

        self.assertEqual(
            controller.sink.commands,
            [
                "RESPAWN_PLAYER_PRACTICE_BRAKED "
                "racer false 10 20 0 1 31.5 8 3",
            ],
        )
        await cancel_tasks(controller)

        controller, player = practice_controller("immediate")
        controller.config["practice_deathzone_protection_enabled"] = True
        player.alive = False
        player.practice_mode = "reset"
        player.practice_map_key = controller.current.key
        controller._prepare_practice_respawn(
            player, 5, 10, 20, 0, 1, speed=31.5, turns=8
        )

        await controller._respawn_player(player)

        self.assertIn(
            "RESPAWN_PLAYER_PRACTICE racer false 10 20 0 1 0 8",
            controller.sink.commands,
        )

    async def test_respawn_start_mode_waits_for_manual_start(self):
        controller, player = practice_controller("respawn")
        player.alive = False
        player.practice_mode = "reset"
        player.practice_map_key = controller.current.key
        controller._prepare_practice_respawn(player, 5, 10, 20, 0, 1)

        await controller._respawn_player(player)

        self.assertFalse(
            any(command.startswith("RESPAWN_PLAYER") for command in controller.sink.commands)
        )
        self.assertTrue(
            any("Type /restart" in plain_console_text(command)
                for command in controller.sink.commands)
        )

    async def test_manual_respawn_always_returns_to_map_start(self):
        controller, player = practice_controller("countdown")
        player.alive = False
        player.practice_mode = "maintain"
        player.practice_map_key = controller.current.key
        controller._prepare_practice_respawn(
            player, 5, 50, 60, 1, 0, speed=45, turns=9
        )

        await controller._command_respawn(player, kill_first=True)

        self.assertIn(
            "RESPAWN_PLAYER_BRAKED racer false 3 4 0 1 3",
            controller.sink.commands,
        )
        self.assertFalse(
            any("50 60" in command for command in controller.sink.commands)
        )
        await cancel_tasks(controller)

    async def test_winzone_does_not_score_or_store_a_practice_finish(self):
        controller, player = practice_controller()
        player.practice_mode = "reset"
        player.practice_map_key = controller.current.key
        player.attempt_started_game = 1.0
        controller.store = Mock()

        payload = "1 finish 0 0 racer 0 0 1 0 12.5"
        await controller._handle_winzone(payload)
        await controller._handle_winzone(payload)

        self.assertEqual(controller.sink.commands.count("KILL_SILENT racer"), 1)
        self.assertFalse(
            any(command.startswith("ADD_SCORE_PLAYER")
                for command in controller.sink.commands)
        )
        controller.store.add_finish.assert_not_called()
        self.assertTrue(
            any(
                "no time or score was recorded" in plain_console_text(command)
                for command in controller.sink.commands
            )
        )

    async def test_enriched_activity_and_death_state_keep_exact_momentum(self):
        controller, player = practice_controller()
        player.practice_mode = "maintain"
        player.practice_map_key = controller.current.key
        player.practice_rewind_seconds = 0

        await controller._handle_player_activity_snapshot(
            "racer 0 1 12 34 9.25 0 1 27.5 6"
        )

        self.assertEqual(player.practice_samples[-1].game_time, 9.25)
        self.assertEqual(player.practice_samples[-1].speed, 27.5)
        self.assertEqual(player.practice_samples[-1].turns, 6)

        controller._handle_replay_begin(
            "token racer 10 12 34 0 1 27.5 6 settings 10.5"
        )
        controller._handle_replay_state(
            "token death 11 40 50 -1 0 42.25 9 260.5"
        )

        snapshot = player.practice_respawn_snapshot
        self.assertIsNotNone(snapshot)
        self.assertEqual(
            (snapshot.x, snapshot.y, snapshot.xdir, snapshot.ydir),
            (40.0, 50.0, -1.0, 0.0),
        )
        self.assertEqual(snapshot.speed, 42.25)
        self.assertEqual(snapshot.turns, 9)
        self.assertEqual(controller.replay_captures["token"].initial_distance, 10.5)
        self.assertEqual(controller.replay_captures["token"].latest_distance, 260.5)

    def test_replay_capture_keeps_exact_resource_and_leaderboard_record_key(self):
        controller, _player = practice_controller()
        controller.current = MapEntry(
            "Author/maps/Practice-v1.aamap.xml",
            "Practice",
            "Author",
            "1",
            "maps",
            "Practice-v1.aamap.xml",
            Path("Practice-v1.aamap.xml"),
            (SpawnPoint(3, 4, 0, 1),),
            record_key="stable-record-key",
        )

        controller._handle_replay_begin("token racer 10 12 34 0 1 27.5 6")

        self.assertEqual(
            controller.replay_captures["token"].resource_key,
            "Author/maps/Practice-v1.aamap.xml",
        )
        self.assertEqual(
            controller.replay_captures["token"].record_key,
            "stable-record-key",
        )

    def test_map_transition_disables_practice(self):
        controller, player = practice_controller()
        player.practice_mode = "reset"
        player.practice_map_key = controller.current.key

        controller._reset_attempts()

        self.assertEqual(player.practice_mode, "off")
        self.assertFalse(controller._practice_active(player))

    def test_native_patch_supplies_exact_practice_state(self):
        root = Path(__file__).resolve().parents[1]
        engine_patch = (root / "engine/patches/tronner-racing.patch").read_text(
            encoding="utf-8"
        )
        server_config = (root / "config/tronner-racing.cfg").read_text(
            encoding="utf-8"
        )

        self.assertIn(
            "cycle->MapPosition().y << se_GameTime() << cycle->Direction().x",
            engine_patch,
        )
        self.assertIn("cycle->Speed() << cycle->GetTurns()", engine_patch)
        self.assertIn(
            'sg_WriteCycleReplayState(this, "death", se_GameTime())',
            engine_patch,
        )
        self.assertIn("RESPAWN_PLAYER_PRACTICE", engine_patch)
        self.assertIn("RESPAWN_PLAYER_PRACTICE_BRAKED", engine_patch)
        self.assertIn("cycle->IsStartHeld(time)", engine_patch)
        self.assertIn("sg_IsPracticeDeathZoneProtected", engine_patch)
        self.assertIn("gDeathZoneHack::OnExit", engine_patch)
        self.assertIn(
            "PRACTICE_DEATHZONE_PROTECTION_TIME 1.0", server_config
        )
        self.assertIn(" /practice ", server_config)


if __name__ == "__main__":
    unittest.main()
