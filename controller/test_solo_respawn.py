import asyncio
import unittest
from pathlib import Path

from TronnerRacing import MapEntry, Player, SpawnPoint, TronnerRacing


def controller_with(*players):
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
    controller.config = {
        "respawn_delay_seconds": 2.0,
        "empty_arena_respawn_delay_seconds": 0.1,
    }
    controller.players = {player.log_name: player for player in players}
    controller.aliases = {
        player.log_name.casefold(): player for player in players
    }
    controller.round_active = True
    controller.transitioning = False
    controller.final_countdown_active = False
    controller.respawn_tasks = {}
    controller.freeze_tasks = {}
    scheduled = []

    def schedule(player, delay_seconds=None):
        scheduled.append((player, delay_seconds))

    controller._schedule_respawn = schedule
    return controller, scheduled


class SoloRespawnTests(unittest.IsolatedAsyncioTestCase):
    async def test_last_alive_racer_uses_saved_respawn_delay(self):
        player = Player("solo", "Solo", alive=True)
        controller, scheduled = controller_with(player)

        await controller._handle_cycle_destroyed("solo 1 2 1 0 Solo 10 DEATHZONE")

        self.assertFalse(player.alive)
        self.assertEqual(scheduled, [(player, 0.0)])

    async def test_same_saved_delay_is_used_while_another_racer_is_alive(self):
        player = Player(
            "first",
            "First",
            alive=True,
            start_respawn_delay_seconds=1.5,
        )
        other = Player("second", "Second", alive=True)
        controller, scheduled = controller_with(player, other)
        controller.start_preferences = {player.identity_key: "immediate 1.5"}

        await controller._handle_cycle_destroyed("first 1 2 1 0 First 10 DEATHZONE")

        self.assertEqual(scheduled, [(player, 1.5)])

    async def test_saved_delay_is_identical_solo_and_multiplayer(self):
        solo = Player("solo", "Solo", alive=True)
        solo_controller, solo_scheduled = controller_with(solo)
        solo_controller.start_preferences = {solo.identity_key: "brake 2.25"}

        multi = Player("multi", "Multi", alive=True)
        other = Player("other", "Other", alive=True)
        multi_controller, multi_scheduled = controller_with(multi, other)
        multi_controller.start_preferences = {multi.identity_key: "brake 2.25"}

        await solo_controller._handle_cycle_destroyed(
            "solo 1 2 1 0 Solo 10 DEATHZONE"
        )
        await multi_controller._handle_cycle_destroyed(
            "multi 1 2 1 0 Multi 10 DEATHZONE"
        )

        self.assertEqual(solo_scheduled, [(solo, 2.25)])
        self.assertEqual(multi_scheduled, [(multi, 2.25)])

    async def test_destroyed_held_spawn_is_rescheduled(self):
        player = Player(
            "solo",
            "Solo",
            alive=True,
            generation=2,
            pending_respawn=True,
            respawn_created_game=12.5,
        )
        controller, scheduled = controller_with(player)
        freeze = asyncio.create_task(asyncio.sleep(60))
        controller.freeze_tasks[id(player)] = freeze

        await controller._handle_cycle_destroyed("solo 3 4 0 1 Solo 12.6 DEATHZONE")
        await asyncio.sleep(0)

        self.assertFalse(player.pending_respawn)
        self.assertIsNone(player.respawn_created_game)
        self.assertEqual(player.generation, 3)
        self.assertTrue(freeze.cancelled())
        self.assertEqual(scheduled, [(player, 0.0)])


if __name__ == "__main__":
    unittest.main()
