import asyncio
import unittest
from pathlib import Path

from TronnerRacing import (
    CheckpointSnapshot,
    MapEntry,
    Player,
    SpawnPoint,
    TronnerRacing,
)


class Sink:
    def __init__(self):
        self.commands = []

    async def send(self, *commands):
        self.commands.extend(commands)


def snapshot():
    return CheckpointSnapshot(
        checkpoint_id=1,
        x=10.0,
        y=20.0,
        xdir=0.0,
        ydir=1.0,
        speed=12.5,
        turns=7,
        event_game=15.0,
        attempt_started_game=10.0,
        checkpoints_collected=frozenset({1}),
        no_cp_elapsed=5.0,
    )


def checkpoint_respawn_controller(mode="brake"):
    controller = object.__new__(TronnerRacing)
    controller.current = MapEntry(
        "map",
        "Map",
        "Author",
        "1",
        "maps",
        "map",
        Path("map"),
        (SpawnPoint(0, 0, 1, 0),),
        checkpoint_ids=(1, 2),
        checkpoint_mode="ordered",
    )
    controller.config = {
        "checkpoint_respawn_delay_seconds": 0,
        "checkpoint_double_respawn_seconds": 1.5,
    }
    controller.sink = Sink()
    controller.freeze_tasks = {}
    controller.respawn_tasks = {}
    controller.center_clear_tasks = {}
    controller.spawn_preferences = {}
    controller.start_preferences = {}
    controller.finalists = set()
    controller.round_active = True
    controller.final_countdown_active = False
    controller.transitioning = False
    controller.respawns_paused = False
    player = Player(
        "racer",
        "Racer",
        alive=False,
        attempt_started_game=10.0,
        start_mode=mode,
        checkpoint_snapshot=snapshot(),
        no_cp_elapsed=5.0,
        no_cp_segment_started_game=15.0,
    )
    controller.start_preferences[player.identity_key] = mode
    controller.players = {"racer": player}
    controller.aliases = {"racer": player}
    return controller, player


async def cancel_tasks(controller):
    tasks = []
    for mapping in (
        controller.freeze_tasks,
        controller.respawn_tasks,
        controller.center_clear_tasks,
    ):
        tasks.extend(mapping.values())
        mapping.clear()
    for task in tasks:
        task.cancel()
    if tasks:
        await asyncio.gather(*tasks, return_exceptions=True)


class CheckpointRespawnTests(unittest.IsolatedAsyncioTestCase):
    async def test_brake_respawn_preserves_checkpoint_state_and_main_timer(self):
        controller, player = checkpoint_respawn_controller("brake")
        player.checkpoint_respawn_requested = True

        await controller._respawn_player(player)
        await asyncio.sleep(0)

        self.assertIn(
            "RESPAWN_PLAYER_CHECKPOINT_BRAKED racer false 10 20 0 1 12.5 7",
            controller.sink.commands,
        )
        controller._handle_cycle_created("racer 10 20 0 1 30")
        self.assertIsNone(player.attempt_started_game)
        self.assertTrue(player.pending_respawn)

        await controller._handle_cycle_released("racer 35")

        self.assertEqual(player.attempt_started_game, 10.0)
        self.assertEqual(player.no_cp_elapsed, 5.0)
        self.assertEqual(player.no_cp_segment_started_game, 35.0)
        self.assertEqual(player.checkpoints_collected, {1})
        self.assertTrue(player.checkpoint_respawn_used)
        self.assertFalse(player.pending_respawn)
        await cancel_tasks(controller)

    async def test_immediate_and_countdown_use_checkpoint_protocol(self):
        immediate, immediate_player = checkpoint_respawn_controller("immediate")
        immediate_player.checkpoint_respawn_requested = True
        await immediate._respawn_player(immediate_player)
        self.assertEqual(
            immediate.sink.commands,
            ["RESPAWN_PLAYER_CHECKPOINT racer false 10 20 0 1 12.5 7"],
        )
        immediate._handle_cycle_created("racer 10 20 0 1 30")
        self.assertEqual(immediate_player.attempt_started_game, 10.0)
        self.assertTrue(immediate_player.checkpoint_respawn_used)

        countdown, countdown_player = checkpoint_respawn_controller("countdown")
        countdown_player.checkpoint_respawn_requested = True
        await countdown._respawn_player(countdown_player)
        self.assertIn(
            "RESPAWN_PLAYER_CHECKPOINT_BRAKED "
            "racer false 10 20 0 1 12.5 7 3",
            countdown.sink.commands,
        )
        self.assertFalse(
            any(command.startswith("FREEZE_PLAYER") for command in countdown.sink.commands)
        )
        await cancel_tasks(countdown)

    async def test_custom_respawn_delay_does_not_change_countdown_length(self):
        controller, player = checkpoint_respawn_controller("countdown")
        controller.start_preferences[player.identity_key] = "countdown 9"
        player.checkpoint_respawn_requested = True

        await controller._respawn_player(player)

        self.assertIn(
            "RESPAWN_PLAYER_CHECKPOINT_BRAKED "
            "racer false 10 20 0 1 12.5 7 3",
            controller.sink.commands,
        )
        self.assertEqual(player.start_respawn_delay_seconds, 9)
        await cancel_tasks(controller)

    async def test_cp_can_replace_an_ordinary_braked_spawn_before_takeoff(self):
        controller, player = checkpoint_respawn_controller("brake")

        await controller._respawn_player(player)
        controller._handle_cycle_created("racer 0 0 1 0 30")
        self.assertIsNotNone(player.checkpoint_snapshot)
        self.assertEqual(player.pending_respawn_kind, "spawn")

        await controller._command_checkpoint_respawn(player)

        self.assertIsNone(player.attempt_started_game)
        self.assertEqual(
            player.checkpoint_snapshot.attempt_started_game,
            10.0,
        )
        self.assertIsNotNone(player.checkpoint_snapshot)
        self.assertTrue(player.checkpoint_respawn_requested)
        self.assertIn("KILL_SILENT racer", controller.sink.commands)
        await cancel_tasks(controller)

    async def test_second_checkpoint_respawn_resets_takeoff_speed(self):
        controller, player = checkpoint_respawn_controller("brake")
        player.alive = True
        player.pending_respawn = True
        player.pending_respawn_kind = "checkpoint"

        await controller._command_checkpoint_respawn(player)

        self.assertEqual(player.checkpoint_respawn_speed, 0.0)
        self.assertTrue(
            any("takeoff speed is now 0" in command for command in controller.sink.commands)
        )
        player.alive = False
        await controller._respawn_player(player)
        self.assertIn(
            "RESPAWN_PLAYER_CHECKPOINT_BRAKED racer false 10 20 0 1 0 7",
            controller.sink.commands,
        )
        await cancel_tasks(controller)


if __name__ == "__main__":
    unittest.main()
