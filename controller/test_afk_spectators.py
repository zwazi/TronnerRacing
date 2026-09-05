import unittest
from unittest import mock

from TronnerRacing import Player, TronnerRacing, plain_console_text


class Sink:
    def __init__(self):
        self.commands = []

    async def send(self, *commands):
        self.commands.extend(commands)


def controller_with(player: Player) -> TronnerRacing:
    controller = object.__new__(TronnerRacing)
    controller.config = {"afk_timeout_seconds": 60}
    controller.sink = Sink()
    controller.players = {player.log_name: player}
    controller.aliases = {player.log_name.casefold(): player}
    controller.extend_votes = set()
    controller.skip_votes = set()
    controller.round_active = False
    controller.transitioning = False
    controller.final_countdown_active = False
    controller.respawns_paused = False
    controller.respawn_tasks = {}
    controller.active_replay_tokens = {}
    controller.replay_captures = {}

    async def resolve_votes():
        return None

    controller._resolve_votes_after_eligibility_change = resolve_votes
    return controller


class SpectatorAfkTests(unittest.IsolatedAsyncioTestCase):
    async def test_idle_spectator_is_not_marked_or_announced_afk(self):
        spectator = Player(
            "spectator",
            "Spectator",
            connected=True,
            active=False,
            respawn_enabled=False,
            last_turn_monotonic=100.0,
        )
        controller = controller_with(spectator)

        await controller._check_afk_players(now=200.0)

        self.assertFalse(spectator.afk)
        self.assertEqual(controller.sink.commands, [])

    async def test_spectator_afk_state_clears_without_announcement(self):
        spectator = Player(
            "spectator",
            "Spectator",
            connected=True,
            active=False,
            respawn_enabled=False,
            afk=True,
        )
        controller = controller_with(spectator)

        await controller._record_player_turn(spectator, 200.0)

        self.assertFalse(spectator.afk)
        self.assertEqual(controller.sink.commands, [])

    async def test_racer_is_afk_exactly_sixty_seconds_after_last_turn(self):
        racer = Player(
            "racer",
            "Racer",
            connected=True,
            active=True,
            alive=True,
            respawn_enabled=True,
            last_turn_monotonic=100.0,
        )
        controller = controller_with(racer)

        await controller._check_afk_players(now=159.9)
        self.assertFalse(racer.afk)

        await controller._check_afk_players(now=160.0)

        self.assertTrue(racer.afk)
        messages = [plain_console_text(item) for item in controller.sink.commands]
        self.assertTrue(any("Racer is now AFK" in item for item in messages))

    async def test_dead_racer_uses_the_same_last_turn_timeout(self):
        racer = Player(
            "racer",
            "Racer",
            connected=True,
            active=True,
            alive=False,
            respawn_enabled=True,
            last_turn_monotonic=100.0,
        )
        controller = controller_with(racer)

        await controller._check_afk_players(now=160.0)

        self.assertTrue(racer.afk)

    async def test_movement_and_other_input_do_not_count_as_a_turn(self):
        racer = Player(
            "racer",
            "Racer",
            connected=True,
            active=True,
            alive=True,
            respawn_enabled=True,
            last_turn_monotonic=30.0,
        )
        controller = controller_with(racer)

        # Native input is fresh and the position has changed, but the engine's
        # last-turn age still points to monotonic time 30.
        with mock.patch("TronnerRacing.time.monotonic", return_value=100.0):
            await controller._handle_player_activity_snapshot(
                "racer 0 1 50 20 10 1 0 30 4 500 70"
            )
        await controller._check_afk_players(now=100.0)

        self.assertEqual(racer.last_turn_monotonic, 30.0)
        self.assertTrue(racer.afk)

    async def test_turn_snapshot_clears_afk_immediately(self):
        racer = Player(
            "racer",
            "Racer",
            connected=True,
            active=True,
            alive=True,
            respawn_enabled=True,
            afk=True,
            last_turn_monotonic=30.0,
        )
        controller = controller_with(racer)

        with mock.patch("TronnerRacing.time.monotonic", return_value=100.0):
            await controller._handle_player_activity_snapshot(
                "racer 20 1 50 20 10 1 0 30 5 500 0"
            )

        self.assertEqual(racer.last_turn_monotonic, 100.0)
        self.assertFalse(racer.afk)
        messages = [plain_console_text(item) for item in controller.sink.commands]
        self.assertTrue(any("Racer is no longer AFK" in item for item in messages))

    async def test_new_cycle_without_a_turn_does_not_reset_the_timer(self):
        racer = Player(
            "racer",
            "Racer",
            connected=True,
            active=True,
            alive=True,
            respawn_enabled=True,
            last_turn_monotonic=30.0,
        )
        controller = controller_with(racer)

        with mock.patch("TronnerRacing.time.monotonic", return_value=100.0):
            await controller._handle_player_activity_snapshot(
                "racer 0 1 0 0 10 1 0 30 1 0 -1"
            )
        await controller._check_afk_players(now=100.0)

        self.assertEqual(racer.last_turn_monotonic, 30.0)
        self.assertTrue(racer.afk)


if __name__ == "__main__":
    unittest.main()
