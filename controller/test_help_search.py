import unittest

from TronnerRacing import (
    USER_COMMAND_HELP,
    Player,
    TronnerRacing,
    search_help_entries,
)


class HelpSearchTests(unittest.IsolatedAsyncioTestCase):
    def test_exact_command_search_returns_every_q_variant(self):
        matches = search_help_entries(USER_COMMAND_HELP, "q")

        self.assertEqual(
            [command for command, _ in matches],
            [
                "/q add [map name]",
                "/q lowest",
                "/q remove [map]",
                "/q clear",
            ],
        )

    def test_description_search_is_case_insensitive(self):
        matches = search_help_entries(USER_COMMAND_HELP, "VOTE")

        self.assertEqual(
            [command for command, _ in matches],
            ["/extend", "/skip"],
        )

    async def test_help_search_uses_help_style_and_respects_access(self):
        controller = object.__new__(TronnerRacing)
        controller.config = {
            "records_admin_access_level": 1,
            "map_admin_access_level": 1,
            "size_admin_access_level": 1,
        }
        controller.hot_commands = None
        racer = Player("racer", "Racer")
        blocks = []
        messages = []

        async def private_block(player, lines):
            blocks.append(list(lines))

        async def private(player, message):
            messages.append(message)

        controller.private_block = private_block
        controller.private = private

        await controller._command_help(racer, 20, "q")

        self.assertEqual(blocks[0][0], 'TronnerRacing commands matching "q":')
        self.assertTrue(all(line.startswith("/q ") for line in blocks[0][1:]))

        await controller._command_help(racer, 20, "resetalltimes")
        self.assertEqual(
            messages[-1],
            'No commands match "resetalltimes". Use /help to list all commands.',
        )

        await controller._command_help(racer, 1, "resetalltimes")
        self.assertIn("/resetalltimes", blocks[-1][1])

    async def test_dispatch_passes_the_search_term_to_help(self):
        controller = object.__new__(TronnerRacing)
        controller.hot_commands = None
        racer = Player("racer", "Racer")
        calls = []

        async def rate_allowed(player):
            return True

        async def help_command(player, access_level, search_term):
            calls.append((player, access_level, search_term))

        controller._command_rate_allowed = rate_allowed
        controller._command_help = help_command

        await controller._dispatch_command("/help", racer, 20, "q")

        self.assertEqual(calls, [(racer, 20, "q")])


if __name__ == "__main__":
    unittest.main()
