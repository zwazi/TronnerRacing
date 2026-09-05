import os
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace

from TronnerRacing import (
    GHOST_LEGACY_NAME_BYTES,
    GHOST_PLAN_FILENAME_RE,
    MapRepository,
    Player,
    Record,
    ReplayCapture,
    ReplayEventState,
    StateStore,
    TronnerRacing as Controller,
    ghost_display_name,
    normalize_ghost_preference,
    plain_console_text,
)


class GhostTests(unittest.IsolatedAsyncioTestCase):
    class Sink:
        def __init__(self):
            self.commands = []

        async def send(self, *commands):
            self.commands.extend(commands)

    class Repository:
        @staticmethod
        def ghost_coordinate_scale(
            _current,
            _recorded_resource_key,
            _recorded_size_factor,
            _current_size_factor,
        ):
            return 1.0

    @staticmethod
    def add_recorded_finish(store: StateStore) -> tuple[Player, Record, int]:
        player = Player("racer", "Racer", auth_name="Racer")
        record, _improved, _old_time, _old_turns = store.add_finish(
            "record-map", player, 12.5, 4
        )
        store.add_replay_settings(
            "physics-1",
            1,
            [(b"CYCLE_START_SPEED", b"20")],
        )
        capture = ReplayCapture(
            token="run-1",
            player_log_name=player.log_name,
            identity_key=player.identity_key,
            username=player.record_name,
            authenticated=True,
            map_identifier="Tester/maps/Race-v1.aamap.xml",
            revision_identifier="revision-1",
            resource_key="resource-revision-1",
            record_key="record-map",
            started_at=1000.0,
            spawn_game_time=10.0,
            x=1.25,
            y=-2.5,
            xdir=1.0,
            ydir=0.0,
            speed=30.0,
            initial_turns=0,
            size_factor=1.0,
            start_mode="countdown",
            checkpoint_spawn=False,
            settings_identifier="physics-1",
            release_offset_us=1_000_000,
            events=[
                (500_000, 0),
                (1_000_000, 2),
                (1_250_000, 0),
                (2_000_000, 3),
            ],
            event_states={
                0: ReplayEventState(0.5, -2.5, 0.0, -1.0, 29.0, 1),
                2: ReplayEventState(2.0, -3.0, 0.0, 1.0, 31.0, 2),
            },
        )
        capture.outcome = "finish"
        capture.finish_seconds = 12.5
        capture.finish_turns = 4
        capture.personal_best = True
        run_id = store.add_replay(capture, 1012.5)
        return player, record, run_id

    @staticmethod
    def add_unfinished_attempt(
        store: StateStore,
        player: Player,
        token: str,
        closest_winzone_distance: float,
        started_at: float,
    ) -> int:
        store.add_replay_settings(
            "physics-1",
            1,
            [(b"CYCLE_START_SPEED", b"20")],
        )
        capture = ReplayCapture(
            token=token,
            player_log_name=player.log_name,
            identity_key=player.identity_key,
            username=player.record_name,
            authenticated=True,
            map_identifier="Tester/maps/Race-v1.aamap.xml",
            revision_identifier="revision-1",
            resource_key="resource-revision-1",
            record_key="record-map",
            started_at=started_at,
            spawn_game_time=10.0,
            x=1.25,
            y=-2.5,
            xdir=1.0,
            ydir=0.0,
            speed=20.0,
            initial_turns=0,
            size_factor=1.0,
            start_mode="countdown",
            checkpoint_spawn=False,
            settings_identifier="physics-1",
            release_offset_us=1_000_000,
            events=[(1_100_000, 0), (3_000_000, 1)],
            closest_winzone_distance=closest_winzone_distance,
        )
        return store.add_replay(capture, started_at + 10.0)

    def test_exact_record_replay_is_normalized_to_race_release(self):
        with tempfile.TemporaryDirectory() as directory:
            store = StateStore(Path(directory) / "state.sqlite3")
            _player, record, run_id = self.add_recorded_finish(store)

            replays = store.ghost_replays_for_record("record-map", record)

            self.assertEqual(len(replays), 1)
            replay = replays[0]
            self.assertEqual(replay.run_id, run_id)
            self.assertEqual(replay.events, ((0, 2), (250_000, 0), (1_000_000, 3)))
            self.assertEqual(
                replay.event_states,
                (None, ReplayEventState(2.0, -3.0, 0.0, 1.0, 31.0, 2), None),
            )
            self.assertEqual(replay.settings_identifier, "physics-1")
            self.assertEqual(replay.resource_key, "resource-revision-1")
            store.close()

    def test_replay_lookup_accepts_historical_record_and_resource_aliases(self):
        with tempfile.TemporaryDirectory() as directory:
            store = StateStore(Path(directory) / "state.sqlite3")
            _player, record, run_id = self.add_recorded_finish(store)
            store.current_connection().execute(
                "UPDATE replay_maps SET record_key='historical-record'"
            )
            store.current_connection().commit()

            replays = store.ghost_replays_for_record(
                "current-record",
                record,
                ("historical-record", "resource-revision-1"),
            )

            self.assertEqual([replay.run_id for replay in replays], [run_id])
            store.close()

    def test_legacy_ghost_name_is_plain_ascii_or_pb_and_0_2_8_safe(self):
        self.assertEqual(ghost_display_name("RacerWithAVeryLongName"), "RacerWithAVeryL")
        self.assertEqual(ghost_display_name("Jörg"), "J?rg")
        self.assertEqual(ghost_display_name("Racer", personal_best=True), "PB")
        self.assertLessEqual(
            len(ghost_display_name("RacerWithAVeryLongName").encode("ascii")),
            GHOST_LEGACY_NAME_BYTES,
        )

    def test_pb_and_rank_preferences_are_canonical_and_durable(self):
        with tempfile.TemporaryDirectory() as directory:
            store = StateStore(Path(directory) / "state.sqlite3")
            controller = object.__new__(Controller)
            controller.store = store
            controller.ghost_preferences = {
                "auth:racer": "pb",
                "auth:other": "rank 7",
            }
            controller.ghost_selections = {}
            controller._save_ghost_preferences()
            controller._clear_ghost_selections()

            self.assertEqual(
                store.get_json("ghost_preferences", {}),
                {"auth:racer": "pb", "auth:other": "rank 7"},
            )
            self.assertEqual(normalize_ghost_preference("personalbest"), "pb")
            self.assertEqual(normalize_ghost_preference("7"), "rank 7")
            self.assertEqual(normalize_ghost_preference("rank 7"), "rank 7")
            self.assertIsNone(normalize_ghost_preference("wr"))
            store.close()

    def test_ghost_settings_allow_tolerated_changes_but_not_other_physics(self):
        with tempfile.TemporaryDirectory() as directory:
            store = StateStore(Path(directory) / "state.sqlite3")
            store.add_replay_settings(
                "recorded",
                1,
                [
                    (b"CYCLE_SPEED", b"20"),
                    (b"CYCLE_RUBBER_MINDISTANCE_UNPREPARED", b"0.005"),
                    (b"PING_CHARITY_SERVER", b"151"),
                    (b"SERVER_OPTIONS", b"Current map: Epyon | Next Map: Retro"),
                ],
            )
            store.add_replay_settings(
                "active",
                1,
                [
                    (b"CYCLE_SPEED", b"20"),
                    (b"CYCLE_RUBBER_MINDISTANCE_UNPREPARED", b"0"),
                    (b"PING_CHARITY_SERVER", b"181"),
                    (b"SERVER_OPTIONS", b"Current map: Epyon | Next Map: Triform"),
                ],
            )
            store.add_replay_settings(
                "changed-physics",
                1,
                [
                    (b"CYCLE_SPEED", b"21"),
                    (b"CYCLE_RUBBER_MINDISTANCE_UNPREPARED", b"0"),
                    (b"PING_CHARITY_SERVER", b"181"),
                    (b"SERVER_OPTIONS", b"Current map: Epyon | Next Map: Triform"),
                ],
            )
            store.add_replay_settings(
                "changed-size",
                1,
                [(b"CYCLE_SPEED", b"20"), (b"SIZE_FACTOR", b"6")],
            )
            store.add_replay_settings(
                "active-size",
                1,
                [(b"CYCLE_SPEED", b"20"), (b"SIZE_FACTOR", b"0")],
            )

            self.assertTrue(store.ghost_settings_compatible("recorded", "active"))
            self.assertFalse(
                store.ghost_settings_compatible("recorded", "changed-physics")
            )
            self.assertFalse(
                store.ghost_settings_compatible("changed-size", "active-size")
            )
            self.assertTrue(
                store.ghost_settings_compatible(
                    "changed-size", "active-size", ignore_size_factor=True
                )
            )
            self.assertFalse(store.ghost_settings_compatible("recorded", "missing"))
            store.close()

    def test_historical_size_baked_map_gets_safe_coordinate_scale(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            public = root / "public"
            legacy = public / "Tester/maps/Race-1.aamap.xml"
            legacy.parent.mkdir(parents=True)
            legacy.write_text(
                '<Resource author="Tester" name="Race" version="1" category="maps">'
                '<Map><Settings><Setting name="SIZE_FACTOR" value="6"/></Settings>'
                '<World><Field><Spawn x="10" y="-2" xdir="1" ydir="0"/>'
                '<Wall><Point x="10" y="-2"/><Point x="12.5" y="3"/>'
                '</Wall></Field></World></Map></Resource>',
                encoding="utf-8",
            )
            current_path = root / "current.aamap.xml"
            current_path.write_text(
                '<Resource author="Tester" name="Race" version="2" category="maps">'
                '<Map><Settings><Setting name="SIZE_FACTOR" value="0"/></Settings>'
                '<World><Field><Spawn x="80" y="-16" xdir="1" ydir="0"/>'
                '<Wall><Point x="80" y="-16"/><Point x="100" y="24"/>'
                '</Wall></Field></World></Map></Resource>',
                encoding="utf-8",
            )
            repository = object.__new__(MapRepository)
            repository.public_dir = public
            repository.firebase_maps_by_key = {}
            repository._ghost_geometry_cache = {}
            current = SimpleNamespace(local_path=current_path)

            scale = repository.ghost_coordinate_scale(
                current,
                "Tester/maps/Race-1.aamap.xml",
                0.0,
                0.0,
            )

            self.assertEqual(scale, 8.0)

            changed = public / "Tester/maps/Race-changed.aamap.xml"
            changed.write_text(
                legacy.read_text(encoding="utf-8").replace(
                    '<Point x="12.5" y="3"/>', '<Point x="13" y="3"/>'
                ),
                encoding="utf-8",
            )
            self.assertIsNone(
                repository.ghost_coordinate_scale(
                    current,
                    "Tester/maps/Race-changed.aamap.xml",
                    0.0,
                    0.0,
                )
            )

    def test_release_state_is_preserved_when_terminal_state_arrives(self):
        capture = ReplayCapture(
            token="run-1",
            player_log_name="racer",
            identity_key="auth:racer",
            username="Racer",
            authenticated=True,
            map_identifier="Tester/maps/Race-v1.aamap.xml",
            revision_identifier="revision-1",
            resource_key="resource-revision-1",
            started_at=1000.0,
            spawn_game_time=10.0,
            x=-8.0,
            y=-136.0,
            xdir=-1.0,
            ydir=0.0,
            speed=0.0,
            initial_turns=0,
            size_factor=1.0,
            start_mode="brake",
            checkpoint_spawn=False,
            initial_distance=12.0,
            latest_distance=12.0,
        )

        capture.update_state(
            10.5, -8.0, -136.0, -1.0, 0.0, 20.0, 1,
            distance=12.0, released=True,
        )
        capture.update_state(
            45.9, 43.0565, -106.419, 0.0, -1.0, 66.0392, 85,
            distance=2604.33,
        )

        self.assertEqual(
            (capture.x, capture.y, capture.xdir, capture.ydir),
            (-8.0, -136.0, -1.0, 0.0),
        )
        self.assertEqual(capture.speed, 20.0)
        self.assertEqual(capture.initial_turns, 1)
        self.assertEqual(capture.release_offset_us, 500_000)
        self.assertEqual(capture.latest_distance, 2604.33)

    def test_begin_state_remains_fallback_without_release(self):
        capture = ReplayCapture(
            token="run-1",
            player_log_name="racer",
            identity_key="auth:racer",
            username="Racer",
            authenticated=True,
            map_identifier="Tester/maps/Race-v1.aamap.xml",
            revision_identifier="revision-1",
            resource_key="resource-revision-1",
            started_at=1000.0,
            spawn_game_time=10.0,
            x=5.0,
            y=7.0,
            xdir=0.0,
            ydir=1.0,
            speed=30.0,
            initial_turns=0,
            size_factor=0.0,
            start_mode="immediate",
            checkpoint_spawn=False,
        )

        capture.update_state(
            20.0, 100.0, 200.0, -1.0, 0.0, 50.0, 6,
            distance=500.0,
        )

        self.assertEqual(
            (capture.x, capture.y, capture.xdir, capture.ydir),
            (5.0, 7.0, 0.0, 1.0),
        )
        self.assertEqual(capture.speed, 30.0)
        self.assertEqual(capture.initial_turns, 0)
        self.assertIsNone(capture.release_offset_us)
        self.assertEqual(capture.latest_distance, 500.0)

    async def test_replay_input_captures_authoritative_post_turn_state(self):
        capture = ReplayCapture(
            token="run-state",
            player_log_name="racer",
            identity_key="auth:racer",
            username="Racer",
            authenticated=True,
            map_identifier="Tester/maps/Race-v1.aamap.xml",
            revision_identifier="revision-1",
            resource_key="resource-revision-1",
            started_at=1000.0,
            spawn_game_time=10.0,
            x=1.0,
            y=2.0,
            xdir=1.0,
            ydir=0.0,
            speed=30.0,
            initial_turns=1,
            size_factor=0.0,
            start_mode="immediate",
            checkpoint_spawn=False,
        )
        controller = object.__new__(Controller)
        controller.replay_captures = {capture.token: capture}
        controller.player_for = lambda _name: None

        await controller._handle_replay_input(
            "run-state 10.25 L 5 -7 0 1 31.5 2"
        )

        self.assertEqual(capture.events, [(250_000, 0)])
        self.assertEqual(
            capture.event_states,
            {0: ReplayEventState(5.0, -7.0, 0.0, 1.0, 31.5, 2)},
        )

    async def test_world_record_command_writes_private_one_shot_plan(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            store = StateStore(root / "state.sqlite3")
            player, _record, run_id = self.add_recorded_finish(store)
            transition_ref = store.add_replay_settings(
                "physics-runtime-update",
                1,
                [(b"SERVER_OPTIONS", b"Next map changed")],
            )
            store.current_connection().execute(
                "INSERT INTO replay_setting_transitions"
                "(run_ref, offset_us, settings_ref) VALUES(?, ?, ?)",
                (run_id, 2_000_000, transition_ref),
            )
            store.current_connection().commit()
            controller = object.__new__(Controller)
            controller.sink = self.Sink()
            controller.store = store
            controller.repository = self.Repository()
            controller.current = SimpleNamespace(
                key="resource-revision-1",
                records_key="record-map",
                time_decimals=3,
            )
            controller.current_size_factor = 1.0
            controller.active_replay_settings_identifier = "physics-1"
            controller.round_active = True
            controller.transitioning = False
            controller.config = {"ghost_plan_dir": str(root / "ghosts")}

            await controller._command_ghost(player, "wr")

            load = next(
                command
                for command in controller.sink.commands
                if command.startswith("GHOST_LOAD ")
            )
            filename = load.rsplit(" ", 1)[1]
            path = root / "ghosts" / filename
            self.assertRegex(filename, GHOST_PLAN_FILENAME_RE)
            self.assertEqual(os.stat(path).st_mode & 0o777, 0o600)
            lines = path.read_text(encoding="ascii").splitlines()
            self.assertEqual(lines[0], "TRONNER_GHOST 2")
            self.assertEqual(lines[1], f"RUN {run_id}")
            self.assertEqual(lines[2], f"NAME {'PB'.encode().hex()}")
            self.assertIn("DURATION_US 12500000", lines)
            self.assertIn("EVENT_COUNT 3", lines)
            self.assertIn("EVENT 0 2 0", lines)
            self.assertIn("EVENT 250000 0 1 2 -3 0 1 31 2", lines)
            confirmation = " ".join(
                plain_console_text(command)
                for command in controller.sink.commands
                if command.startswith("PLAYER_MESSAGE ")
            )
            self.assertIn("private ghost", confirmation)
            self.assertIn("next attempt", confirmation)

            controller.sink.commands.clear()
            await controller._command_ghost(player, "")
            self.assertTrue(
                any(
                    "Selected PB" in plain_console_text(command)
                    for command in controller.sink.commands
                )
            )
            store.close()

    async def test_ghost_allows_different_physics_and_can_be_disabled(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            store = StateStore(root / "state.sqlite3")
            player, _record, _run_id = self.add_recorded_finish(store)
            controller = object.__new__(Controller)
            controller.sink = self.Sink()
            controller.store = store
            controller.repository = self.Repository()
            controller.current = SimpleNamespace(
                key="resource-revision-1",
                records_key="record-map",
                time_decimals=3,
            )
            controller.current_size_factor = 1.0
            controller.active_replay_settings_identifier = "physics-2"
            controller.round_active = True
            controller.transitioning = False
            controller.config = {"ghost_plan_dir": str(root / "ghosts")}

            await controller._command_ghost(player, "pb")
            self.assertTrue(
                any(command.startswith("GHOST_LOAD ") for command in controller.sink.commands)
            )
            self.assertFalse(
                any(
                    "different server physics" in plain_console_text(command)
                    for command in controller.sink.commands
                )
            )

            controller.sink.commands.clear()
            await controller._command_ghost(player, "off")
            self.assertIn("GHOST_CLEAR racer", controller.sink.commands)
            store.close()

    async def test_zero_speed_legacy_finish_uses_recorded_start_setting(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            store = StateStore(root / "state.sqlite3")
            player, _record, run_id = self.add_recorded_finish(store)
            store.current_connection().execute(
                "UPDATE replay_runs SET start_speed=0 WHERE id=?", (run_id,)
            )
            store.current_connection().commit()
            controller = object.__new__(Controller)
            controller.sink = self.Sink()
            controller.store = store
            controller.repository = self.Repository()
            controller.current = SimpleNamespace(
                key="resource-revision-1",
                records_key="record-map",
                time_decimals=3,
            )
            controller.current_size_factor = 1.0
            controller.active_replay_settings_identifier = "physics-1"
            controller.round_active = True
            controller.transitioning = False
            controller.config = {"ghost_plan_dir": str(root / "ghosts")}

            await controller._command_ghost(player, "pb")

            load = next(
                command
                for command in controller.sink.commands
                if command.startswith("GHOST_LOAD ")
            )
            plan = root / "ghosts" / load.rsplit(" ", 1)[1]
            self.assertIn("START 1.25 -2.5 1 0 20 0", plan.read_text())
            store.close()

    async def test_selected_pb_is_reloaded_when_its_replay_updates(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            store = StateStore(root / "state.sqlite3")
            player, _record, old_run_id = self.add_recorded_finish(store)
            controller = object.__new__(Controller)
            controller.sink = self.Sink()
            controller.store = store
            controller.repository = self.Repository()
            controller.current = SimpleNamespace(
                key="resource-revision-1",
                records_key="record-map",
                time_decimals=3,
            )
            controller.current_size_factor = 1.0
            controller.active_replay_settings_identifier = "physics-1"
            controller.round_active = True
            controller.transitioning = False
            controller.config = {"ghost_plan_dir": str(root / "ghosts")}
            controller.players = {"racer": player}

            await controller._command_ghost(player, "pb")
            self.assertEqual(
                controller.ghost_selections[player.identity_key]["runId"],
                old_run_id,
            )
            store.add_finish("record-map", player, 11.0, 3)
            capture = ReplayCapture(
                token="run-2",
                player_log_name=player.log_name,
                identity_key=player.identity_key,
                username=player.record_name,
                authenticated=True,
                map_identifier="Tester/maps/Race-v1.aamap.xml",
                revision_identifier="revision-1",
                resource_key="resource-revision-1",
                record_key="record-map",
                started_at=2000.0,
                spawn_game_time=20.0,
                x=1.25,
                y=-2.5,
                xdir=1.0,
                ydir=0.0,
                speed=20.0,
                initial_turns=0,
                size_factor=1.0,
                start_mode="countdown",
                checkpoint_spawn=False,
                settings_identifier="physics-1",
                events=[(100_000, 0)],
            )
            capture.outcome = "finish"
            capture.finish_seconds = 11.0
            capture.finish_turns = 3
            capture.personal_best = True
            new_run_id = store.add_replay(capture, 2011.0)
            controller.sink.commands.clear()

            await controller._refresh_ghost_selections("record-map")

            self.assertTrue(
                any(
                    command.startswith("GHOST_LOAD ")
                    for command in controller.sink.commands
                )
            )
            self.assertEqual(
                controller.ghost_selections[player.identity_key]["runId"],
                new_run_id,
            )
            self.assertTrue(
                any(
                    "ghost was updated" in plain_console_text(command)
                    for command in controller.sink.commands
                )
            )
            store.close()

    async def test_command_uses_fastest_available_run_when_pb_predates_capture(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            store = StateStore(root / "state.sqlite3")
            player, _record, _run_id = self.add_recorded_finish(store)
            record, improved, _old_time, _old_turns = store.add_finish(
                "record-map", player, 11.0, 3
            )
            self.assertTrue(improved)
            controller = object.__new__(Controller)
            controller.sink = self.Sink()
            controller.store = store
            controller.repository = self.Repository()
            controller.current = SimpleNamespace(
                key="resource-revision-2",
                records_key="record-map",
                time_decimals=3,
            )
            controller.current_size_factor = 0.0
            controller.active_replay_settings_identifier = "physics-1"
            controller.round_active = True
            controller.transitioning = False
            controller.config = {"ghost_plan_dir": str(root / "ghosts")}

            await controller._command_ghost(player, "pb")

            self.assertTrue(
                any(
                    command.startswith("GHOST_LOAD ")
                    for command in controller.sink.commands
                )
            )
            confirmation = " ".join(
                plain_console_text(command)
                for command in controller.sink.commands
                if command.startswith("PLAYER_MESSAGE ")
            )
            self.assertIn("fastest available replay", confirmation)
            self.assertIn("12.500s", confirmation)
            self.assertIn("ranked time 11.000s", confirmation)
            self.assertEqual(record.best_seconds, 11.0)
            store.close()

    async def test_unfinished_pb_uses_closest_progress_until_first_finish(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            store = StateStore(root / "state.sqlite3")
            player = Player("racer", "Racer", auth_name="Racer")
            farther_run_id = self.add_unfinished_attempt(
                store, player, "farther", 40.0, 1000.0
            )

            controller = object.__new__(Controller)
            controller.sink = self.Sink()
            controller.store = store
            controller.repository = self.Repository()
            controller.current = SimpleNamespace(
                key="resource-revision-1",
                records_key="record-map",
                time_decimals=3,
            )
            controller.current_size_factor = 1.0
            controller.active_replay_settings_identifier = "physics-1"
            controller.round_active = True
            controller.transitioning = False
            controller.config = {"ghost_plan_dir": str(root / "ghosts")}
            player.connected = True
            controller.players = {player.log_name: player}

            await controller._command_ghost(player, "pb")

            self.assertEqual(
                controller.ghost_selections[player.identity_key]["runId"],
                farther_run_id,
            )
            self.assertEqual(
                controller.ghost_selections[player.identity_key]["ghostName"],
                "PB",
            )
            self.assertEqual(
                store.get_json("ghost_preferences", {}).get(player.identity_key),
                "pb",
            )
            confirmation = " ".join(
                plain_console_text(command)
                for command in controller.sink.commands
                if command.startswith("PLAYER_MESSAGE ")
            )
            self.assertIn("closest unfinished attempt", confirmation)

            closer_run_id = self.add_unfinished_attempt(
                store, player, "closer", 12.0, 2000.0
            )
            candidates = store.ghost_replays_for_unfinished_pb(
                "record-map", player.identity_key
            )
            self.assertEqual(
                [replay.run_id for replay in candidates],
                [closer_run_id, farther_run_id],
            )
            self.assertFalse(candidates[0].finished)
            self.assertEqual(candidates[0].closest_winzone_distance, 12.0)
            self.assertEqual(candidates[0].finish_seconds, 9.0)
            controller.sink.commands.clear()
            await controller._refresh_ghost_selections("record-map")
            self.assertEqual(
                controller.ghost_selections[player.identity_key]["runId"],
                closer_run_id,
            )
            self.assertTrue(
                any(
                    "closest unfinished attempt" in plain_console_text(command)
                    for command in controller.sink.commands
                )
            )

            _finished_player, _record, finished_run_id = self.add_recorded_finish(store)
            controller.sink.commands.clear()
            await controller._command_ghost(player, "pb")

            self.assertEqual(
                controller.ghost_selections[player.identity_key]["runId"],
                finished_run_id,
            )
            self.assertTrue(
                store.ghost_replays_for_record(
                    "record-map", store.records("record-map")[0]
                )[0].finished
            )
            store.close()

    async def test_rank_preference_restores_before_the_next_round_spawn(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            store = StateStore(root / "state.sqlite3")
            player, _record, run_id = self.add_recorded_finish(store)
            player.connected = True
            controller = object.__new__(Controller)
            controller.sink = self.Sink()
            controller.store = store
            controller.repository = self.Repository()
            controller.current = SimpleNamespace(
                key="resource-revision-1",
                records_key="record-map",
                time_decimals=3,
            )
            controller.current_size_factor = 1.0
            controller.active_replay_settings_identifier = "physics-1"
            controller.round_active = True
            controller.transitioning = False
            controller.config = {"ghost_plan_dir": str(root / "ghosts")}
            controller.players = {player.log_name: player}
            controller.ghost_preferences = {}
            controller.ghost_selections = {}

            await controller._command_ghost(player, "1")
            self.assertEqual(
                store.get_json("ghost_preferences", {}).get(player.identity_key),
                "rank 1",
            )
            controller.ghost_selections = {}
            controller.sink.commands.clear()
            await controller._restore_persistent_ghosts_for_round()

            self.assertEqual(
                controller.ghost_selections[player.identity_key]["runId"], run_id
            )
            self.assertEqual(
                controller.ghost_selections[player.identity_key]["selector"],
                "rank 1",
            )
            self.assertTrue(
                any(
                    command.startswith("GHOST_LOAD ")
                    for command in controller.sink.commands
                )
            )
            store.close()

    def test_replay_progress_keeps_the_closest_route_field_distance(self):
        capture = ReplayCapture(
            token="progress",
            player_log_name="racer",
            identity_key="auth:racer",
            username="Racer",
            authenticated=True,
            map_identifier="map",
            revision_identifier="revision",
            resource_key="resource-revision-1",
            started_at=1000.0,
            spawn_game_time=10.0,
            x=0.0,
            y=0.0,
            xdir=1.0,
            ydir=0.0,
            speed=20.0,
            initial_turns=0,
            size_factor=1.0,
            start_mode="countdown",
            checkpoint_spawn=False,
        )
        controller = object.__new__(Controller)
        controller.current = SimpleNamespace(key="resource-revision-1")
        controller.final_countdown_route_map_key = "resource-revision-1"
        controller.final_countdown_route_model = SimpleNamespace(
            distance_at=lambda position: position[0]
        )

        controller._record_replay_route_progress(capture, (50.0, 0.0))
        controller._record_replay_route_progress(capture, (12.0, 0.0))
        controller._record_replay_route_progress(capture, (20.0, 0.0))

        self.assertEqual(capture.closest_winzone_distance, 12.0)

    def test_rank_and_name_selectors_are_unambiguous(self):
        records = [
            Record("auth:alice", "Alice", 10.0, True),
            Record("auth:bob", "Bob", 11.0, True),
            Record("auth:bobby", "Bobby", 12.0, True),
        ]
        player = Player("alice", "Alice", auth_name="Alice")

        record, rank, label = Controller._ghost_record_for_selector(
            records, player, "rank 2"
        )
        self.assertEqual((record.username, rank, label), ("Bob", 2, "rank 2"))
        record, rank, label = Controller._ghost_record_for_selector(
            records, player, "Alice"
        )
        self.assertEqual((record.username, rank, label), ("Alice", 1, "Alice"))
        record, rank, message = Controller._ghost_record_for_selector(
            records, player, "Bo"
        )
        self.assertIsNone(record)
        self.assertIsNone(rank)
        self.assertIn("ambiguous", message)


if __name__ == "__main__":
    unittest.main()
