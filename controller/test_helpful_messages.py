import tempfile
import time
import unittest
from pathlib import Path
from unittest.mock import patch

from TronnerRacing import (
    Player,
    TronnerRacing,
    load_helpful_messages,
    plain_console_text,
)


class Sink:
    def __init__(self):
        self.commands = []

    async def send(self, *commands):
        self.commands.extend(commands)


class HelpfulMessageTests(unittest.IsolatedAsyncioTestCase):
    def test_document_uses_one_message_per_non_comment_line(self):
        with tempfile.TemporaryDirectory() as temporary_directory:
            path = Path(temporary_directory) / "messages.txt"
            path.write_text(
                "# Helpful messages\n\nFirst message.\n  Second message.  \n",
                encoding="utf-8",
            )

            self.assertEqual(
                load_helpful_messages(path),
                ["First message.", "Second message."],
            )

    async def test_announcements_alternate_and_skip_an_empty_server(self):
        with tempfile.TemporaryDirectory() as temporary_directory:
            path = Path(temporary_directory) / "messages.txt"
            path.write_text("First message.\nSecond message.\n", encoding="utf-8")
            controller = object.__new__(TronnerRacing)
            controller.config = {"helpful_messages_file": str(path)}
            controller.helpful_message_cycle = {}
            controller.players = {}
            controller.sink = Sink()

            await controller._announce_helpful_message_once()
            self.assertEqual(controller.sink.commands, [])
            self.assertEqual(controller.helpful_message_cycle, {})

            player = Player(
                "racer",
                "Racer",
                connected=True,
                active=True,
                last_turn_monotonic=time.monotonic(),
            )
            controller.players[player.log_name] = player
            with patch("TronnerRacing.random.shuffle", side_effect=lambda items: None):
                await controller._announce_helpful_message_once()
                await controller._announce_helpful_message_once()

            messages = [
                plain_console_text(command)
                for command in controller.sink.commands
            ]
            self.assertEqual(
                messages,
                [
                    "CONSOLE_MESSAGE First message.",
                    "CONSOLE_MESSAGE Second message.",
                ],
            )
            self.assertEqual(controller.helpful_message_cycle["index"], 2)

    async def test_spectators_and_stale_players_do_not_trigger_messages(self):
        with tempfile.TemporaryDirectory() as temporary_directory:
            path = Path(temporary_directory) / "messages.txt"
            path.write_text("Message.\n", encoding="utf-8")
            controller = object.__new__(TronnerRacing)
            controller.config = {
                "helpful_messages_file": str(path),
                "helpful_message_activity_window_seconds": 180,
            }
            controller.helpful_message_cycle = {}
            controller.sink = Sink()
            spectator = Player(
                "spectator",
                "Spectator",
                connected=True,
                active=False,
                last_turn_monotonic=time.monotonic(),
            )
            stale_racer = Player(
                "afk",
                "AFK",
                connected=True,
                active=True,
                last_turn_monotonic=time.monotonic() - 181,
            )
            controller.players = {
                spectator.log_name: spectator,
                stale_racer.log_name: stale_racer,
            }

            await controller._announce_helpful_message_once()

            self.assertEqual(controller.sink.commands, [])

    async def test_ai_players_do_not_trigger_announcements(self):
        with tempfile.TemporaryDirectory() as temporary_directory:
            path = Path(temporary_directory) / "messages.txt"
            path.write_text("Message.\n", encoding="utf-8")
            controller = object.__new__(TronnerRacing)
            controller.config = {"helpful_messages_file": str(path)}
            controller.helpful_message_cycle = {}
            ai = Player(
                "bot",
                "Bot",
                connected=True,
                active=True,
                is_ai=True,
                last_turn_monotonic=time.monotonic(),
            )
            controller.players = {ai.log_name: ai}
            controller.sink = Sink()

            await controller._announce_helpful_message_once()

            self.assertEqual(controller.sink.commands, [])

    async def test_every_message_is_shown_before_the_cycle_repeats(self):
        with tempfile.TemporaryDirectory() as temporary_directory:
            path = Path(temporary_directory) / "messages.txt"
            path.write_text("First.\nSecond.\nThird.\n", encoding="utf-8")
            controller = object.__new__(TronnerRacing)
            controller.config = {"helpful_messages_file": str(path)}
            controller.helpful_message_cycle = {}
            controller.sink = Sink()
            player = Player(
                "racer",
                "Racer",
                connected=True,
                active=True,
                last_turn_monotonic=time.monotonic(),
            )
            controller.players = {player.log_name: player}

            for _ in range(6):
                await controller._announce_helpful_message_once()

            messages = [
                plain_console_text(command).removeprefix("CONSOLE_MESSAGE ")
                for command in controller.sink.commands
            ]
            self.assertEqual(set(messages[:3]), {"First.", "Second.", "Third."})
            self.assertEqual(set(messages[3:]), {"First.", "Second.", "Third."})
            self.assertNotEqual(messages[2], messages[3])

    async def test_round_schedules_exactly_one_message_at_a_random_time(self):
        with tempfile.TemporaryDirectory() as temporary_directory:
            path = Path(temporary_directory) / "messages.txt"
            path.write_text("Message.\n", encoding="utf-8")
            controller = object.__new__(TronnerRacing)
            controller.config = {
                "helpful_messages_file": str(path),
                "helpful_message_random_min_seconds": 0,
                "helpful_message_random_max_seconds": 0,
            }
            controller.helpful_message_cycle = {}
            controller.helpful_message_round_generation = 0
            controller.helpful_message_announced = False
            controller._helpful_message_task = None
            controller.round_active = True
            controller.transitioning = False
            controller.final_countdown_active = False
            controller.deadline_epoch = time.time() + 300
            controller.sink = Sink()
            player = Player(
                "racer",
                "Racer",
                connected=True,
                active=True,
                last_turn_monotonic=time.monotonic(),
            )
            controller.players = {player.log_name: player}

            with patch("TronnerRacing.random.uniform", return_value=0) as uniform:
                controller._schedule_helpful_message()
                task = controller._helpful_message_task
                await task

            uniform.assert_called_once_with(0.0, 0.0)
            self.assertEqual(
                [plain_console_text(command) for command in controller.sink.commands],
                ["CONSOLE_MESSAGE Message."],
            )
            self.assertTrue(controller.helpful_message_announced)
            self.assertIsNone(controller._helpful_message_task)

            controller._schedule_helpful_message()
            self.assertIsNone(controller._helpful_message_task)
            self.assertEqual(len(controller.sink.commands), 1)


if __name__ == "__main__":
    unittest.main()
