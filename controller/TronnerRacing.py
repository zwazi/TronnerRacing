#!/usr/bin/env python3
"""Tronner Racing server script for an Armagetron sty+ct+ap dedicated server.

The server script follows ladderlog.txt, writes commands to the server's input
stream, mirrors maps from the configured Git repository over plain HTTP for
legacy clients, and stores race records in SQLite.
"""

from __future__ import annotations

import argparse
import asyncio
import codecs
import collections
import contextlib
import dataclasses
import datetime
import functools
import hashlib
import http.server
import ipaddress
import json
import logging
import math
import os
import random
import re
import resource
import shutil
import signal
import socket
import sqlite3
import subprocess
import threading
import time
import unicodedata
import urllib.error
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
import zlib
from pathlib import Path
from typing import Iterable, Sequence
from zoneinfo import ZoneInfo, ZoneInfoNotFoundError

from firebase_catalog import FirebaseCatalogClient, FirebaseCatalogError
from final_countdown_guard import (
    AccelerationCapability,
    PlayerProgressState,
    RouteModel,
    load_or_build_route_model,
)
from live_dashboard import FirebaseLiveDashboardPublisher, public_player_id


LOG = logging.getLogger("TronnerRacing")
MAP_SUFFIX = ".aamap.xml"
RESEND_ENDPOINT = "https://api.resend.com/emails"
# Account linking is an optional operator integration. Never default a public
# source build to somebody else's billable endpoint.
DEFAULT_GAME_LINK_ENDPOINT = ""
DEFAULT_GAME_TEXT_ENCODING = "latin-1"
REPLAY_FORMAT_VERSION = 1
REPLAY_ACTION_CODES = {"L": 0, "R": 1, "B0": 2, "B1": 3}
REPLAY_ACTION_NAMES = tuple(REPLAY_ACTION_CODES)
REPLAY_SETTINGS_FORMAT_VERSION = 1
GHOST_PLAN_FORMAT_VERSION = 2
GHOST_MAX_EVENTS = 100_000
GHOST_MAX_DURATION_SECONDS = 3_600.0
GHOST_REPLAY_CANDIDATE_LIMIT = 100
# Armagetron 0.2.8 stores a player name in a tString whose 16-character limit
# includes its terminating NUL.  Keep server-created ghost names to 15 visible
# ASCII bytes so legacy clients never have to truncate them.
GHOST_LEGACY_NAME_BYTES = 15
# These settings are captured in replay snapshots but cannot affect the path of
# a private, server-driven ghost. Their values routinely change as players or
# the map queue change, so comparing the raw snapshot identifier would reject
# otherwise identical physics.
GHOST_NON_PHYSICS_REPLAY_SETTINGS = frozenset(
    {b"PING_CHARITY_SERVER", b"SERVER_OPTIONS"}
)
# Historical ghosts remain useful when this grind-depth safeguard changes.
# Ghost plans are private, non-colliding playback objects, and current plans
# restore authoritative cycle state at turns, so this difference must not make
# a previously captured run unavailable.
GHOST_TOLERATED_PHYSICS_REPLAY_SETTINGS = frozenset(
    {b"CYCLE_RUBBER_MINDISTANCE_UNPREPARED"}
)
GHOST_SPATIAL_MAP_ATTRIBUTES = frozenset(
    {"x", "y", "radius", "growth", "destX", "destY"}
)
GHOST_PLAN_FILENAME_RE = re.compile(r"ghost-[0-9]+-[0-9]+\.plan")
SERVER_CONSOLE_HISTORY_LINES = 250
SERVER_CONSOLE_INITIAL_LINES = 100
SERVER_CONSOLE_BATCH_SIZE = 25
SERVER_CONSOLE_STREAM_SECONDS = 90.0
SERVER_CONSOLE_MAX_FILE_BYTES = 8 * 1024 * 1024
MAP_HISTORY_LIMIT = 25
UPCOMING_ROTATION_LIMIT = 25
FINAL_COUNTDOWN_CENTER_PADDING = 20
PLAYER_MESSAGE_LIMIT = 512
PLAYER_MESSAGE_PENDING_LIMIT = 25
PLAYER_MESSAGE_GLOBAL_LIMIT = 5000
DEFAULT_START_COUNTDOWN_SECONDS = 3
DEFAULT_START_RESPAWN_DELAY_SECONDS = 0.0
MIN_START_RESPAWN_DELAY_SECONDS = 0.0
MAX_START_RESPAWN_DELAY_SECONDS = 60.0
START_MODES = frozenset({"brake", "immediate", "countdown", "respawn"})
START_PREFERENCES_STORAGE_KEY = "start_preferences_v2"
PRACTICE_MODES = frozenset({"reset", "maintain"})
DEFAULT_PRACTICE_MAX_REWIND_SECONDS = 300.0
SERVER_CONSOLE_SENSITIVE_RE = re.compile(
    r"(?i)\b(?:admin[_-]?pass|password|passphrase|secret|api[_-]?key|"
    r"authorization|bearer|private[_-]?key)\b"
)
SERVER_MANAGEMENT_COMMANDS = frozenset(
    {
        "announce",
        "direct_message",
        "kick",
        "ban",
        "silence",
        "voice",
        "kill",
        "force_skip",
        "end_map",
        "queue_map",
        "remove_queued_map",
        "clear_queue",
        "change_map",
        "reload_maps",
        "restart_round",
        "restart_server",
        "web_chat",
        "console_command",
        "set_engine_option",
        "reload_server_script",
        # Compatibility for commands queued by an older web release.
        "reload_controller",
        "start_console_stream",
    }
)
SERVER_MANAGEMENT_ENGINE_OPTIONS = {
    "IDLE_KICK_TIME": (0.0, 86_400.0),
    "SPAM_AUTOKICK": (0.0, 10_000.0),
    "SPAM_AUTOKICK_COUNT": (0.0, 1_000.0),
    "MAX_CLIENTS": (1.0, 64.0),
    "MAX_PLAYERS": (1.0, 64.0),
    "VOTING_ALLOWED": (0.0, 1.0),
    "VOTING_KICK_TIME": (0.0, 86_400.0),
    "CYCLE_RUBBER": (0.0, 100.0),
    "CYCLE_SPEED": (0.01, 1_000.0),
    "CYCLE_ACCEL": (0.0, 1_000.0),
    "CYCLE_BRAKE": (0.0, 1.0),
}


def normalize_start_preference(value: object) -> str | None:
    """Return one canonical start mode and its post-death respawn delay."""
    parts = str(value).strip().casefold().split()
    if not parts or parts[0] not in START_MODES:
        return None
    mode = parts[0]
    if len(parts) == 1:
        return mode
    if len(parts) != 2 or not re.fullmatch(r"[0-9]+(?:\.[0-9]+)?", parts[1]):
        return None
    seconds = float(parts[1])
    if not MIN_START_RESPAWN_DELAY_SECONDS <= seconds <= MAX_START_RESPAWN_DELAY_SECONDS:
        return None
    return mode if seconds == 0 else f"{mode} {seconds:g}"


def normalize_ghost_preference(value: object) -> str | None:
    """Return the durable subset of ghost selectors in canonical form."""
    parts = plain_console_text(value).strip().casefold().split()
    if not parts:
        return "pb"
    if parts[0] in {"pb", "personal", "personalbest"} and len(parts) == 1:
        return "pb"
    if len(parts) == 1 and parts[0].isdigit():
        rank_text = parts[0]
    elif len(parts) == 2 and parts[0] == "rank" and parts[1].isdigit():
        rank_text = parts[1]
    else:
        return None
    rank = int(rank_text)
    return f"rank {rank}" if rank > 0 else None


def start_preference_details(value: object) -> tuple[str, float, str]:
    """Return mode, respawn delay, and canonical persisted preference."""
    preference = normalize_start_preference(value) or "immediate"
    parts = preference.split()
    seconds = float(parts[1]) if len(parts) == 2 else 0.0
    return parts[0], seconds, preference


def _ascii_compatible_encoding(value: object) -> str | None:
    """Resolve a Python codec that preserves Armagetron's ASCII protocol."""
    candidate = str(value).strip()
    if not candidate:
        return None
    try:
        encoding = codecs.lookup(candidate).name
        probe = "ENCODING".encode(encoding)
        if probe != b"ENCODING" or probe.decode(encoding) != "ENCODING":
            return None
        return encoding
    except (LookupError, UnicodeError):
        return None


def canonical_game_text_encoding(
    value: object,
    fallback: object = DEFAULT_GAME_TEXT_ENCODING,
) -> str:
    """Normalize advertised codec names and reject non-text protocol codecs."""
    fallback_encoding = (
        _ascii_compatible_encoding(fallback)
        or _ascii_compatible_encoding(DEFAULT_GAME_TEXT_ENCODING)
        or "iso8859-1"
    )
    encoding = _ascii_compatible_encoding(value)
    if encoding is None:
        LOG.warning(
            "unsupported Armagetron text encoding %r; using %s",
            value,
            fallback_encoding,
        )
        return fallback_encoding
    return encoding


def detect_game_text_encoding(
    ladderlog: Path,
    fallback: object = DEFAULT_GAME_TEXT_ENCODING,
) -> str:
    """Return the newest encoding visible at the bounded edges of ladderlog."""
    fallback_encoding = canonical_game_text_encoding(fallback)
    advertised: bytes | None = None
    try:
        with ladderlog.open("rb") as handle:
            size = os.fstat(handle.fileno()).st_size
            head_bytes = 64 * 1024
            tail_bytes = 1024 * 1024
            if size <= head_bytes + tail_bytes:
                chunks = (handle.read(),)
            else:
                chunks = [handle.read(head_bytes)]
                handle.seek(max(0, size - tail_bytes))
                handle.readline()  # Discard the partial line at the tail boundary.
                chunks.append(handle.read(tail_bytes))
            for raw_line in b"\n".join(chunks).splitlines():
                if raw_line.startswith(b"ENCODING "):
                    fields = raw_line[len(b"ENCODING "):].strip().split()
                    if fields:
                        advertised = fields[0]
    except OSError:
        return fallback_encoding
    if advertised is None:
        return fallback_encoding
    try:
        name = advertised.decode("ascii")
    except UnicodeDecodeError:
        LOG.warning(
            "non-ASCII Armagetron ENCODING declaration; using %s",
            fallback_encoding,
        )
        return fallback_encoding
    return canonical_game_text_encoding(name, fallback_encoding)


def decode_game_text(data: bytes, encoding: str, context: str) -> str:
    """Decode protocol bytes, reporting corruption instead of hiding it."""
    try:
        return data.decode(encoding)
    except UnicodeDecodeError as error:
        LOG.warning(
            "invalid %s data in %s at byte %d; replacing undecodable bytes",
            encoding,
            context,
            error.start,
        )
        return data.decode(encoding, "replace")


def encode_game_text(text: str, encoding: str, context: str) -> bytes:
    """Encode protocol text and safely degrade unsupported Unicode characters."""
    try:
        return text.encode(encoding)
    except UnicodeEncodeError as error:
        LOG.warning(
            "%s contains characters unsupported by %s at character %d; replacing them",
            context,
            encoding,
            error.start,
        )
        return text.encode(encoding, "replace")


def local_name(tag: str) -> str:
    return tag.rsplit("}", 1)[-1]


def ghost_map_geometry(path: Path, size_factor: float) -> tuple | None:
    """Return a strict, size-normalized representation of a map's geometry."""
    try:
        factor = float(size_factor)
        if not math.isfinite(factor) or abs(factor) > 100:
            return None
        scale = 2.0 ** (factor / 2.0)
        root = ET.parse(path).getroot()
        map_node = next(node for node in root.iter() if local_name(node.tag) == "Map")
    except (
        ET.ParseError,
        OSError,
        StopIteration,
        TypeError,
        ValueError,
        OverflowError,
    ):
        return None

    def canonical(node: ET.Element) -> tuple:
        attributes: list[tuple[str, str]] = []
        for raw_name, raw_value in node.attrib.items():
            name = local_name(raw_name)
            value = raw_value.strip()
            if name in GHOST_SPATIAL_MAP_ATTRIBUTES:
                try:
                    physical = float(value) * scale
                except (TypeError, ValueError, OverflowError) as exc:
                    raise ValueError("invalid spatial map coordinate") from exc
                if not math.isfinite(physical):
                    raise ValueError("non-finite spatial map coordinate")
                physical = round(physical, 5)
                if physical == 0:
                    physical = 0.0
                value = format(physical, ".5f")
            attributes.append((name, value))
        children: list[tuple] = []
        for child in node:
            if local_name(child.tag) != "Settings":
                children.append(canonical(child))
        return (
            local_name(node.tag),
            tuple(sorted(attributes)),
            " ".join((node.text or "").split()),
            tuple(children),
        )

    try:
        return canonical(map_node)
    except ValueError:
        return None


def ghost_display_name(username: object, personal_best: bool = False) -> str:
    """Build a plain player/PB label within the 0.2.8 name limit."""
    if personal_best:
        return "PB"
    player_bytes = plain_console_text(username).encode("ascii", "replace")
    return player_bytes[:GHOST_LEGACY_NAME_BYTES].decode("ascii") or "?"


def clean_console_text(value: object) -> str:
    return str(value).replace("\r", " ").replace("\n", " ").strip()


def normalized_connection_ip(value: object) -> str:
    """Extract one canonical IP from a ladderlog connection address."""
    address = clean_console_text(value)
    candidates = [address]
    if address.startswith("[") and "]" in address:
        candidates.insert(0, address[1:address.index("]")])
    elif address.count(":") == 1:
        host, port = address.rsplit(":", 1)
        if port.isdigit():
            candidates.insert(0, host)
    for candidate in candidates:
        try:
            return str(ipaddress.ip_address(candidate))
        except ValueError:
            continue
    return address[:128]


def quote_console(value: object) -> str:
    text = clean_console_text(value).replace("\\", "\\\\").replace('"', '\\"')
    return f'"{text}"'


def quote_console_exact(value: object) -> str:
    """Quote trusted text without trimming intentional edge whitespace."""
    text = str(value).replace("\r", " ").replace("\n", " ")
    text = text.replace("\\", "\\\\").replace('"', '\\"')
    return f'"{text}"'


def quote_console_block(value: object) -> str:
    """Quote a multiline argument using the console parser's ``\\n`` escape."""
    text = str(value).replace("\r\n", "\n").replace("\r", "\n")
    text = text.replace("\\", "\\\\").replace('"', '\\"')
    text = text.replace("\n", "\\n")
    return f'"{text}"'


def readline_console_text(value: object) -> str:
    """Escape text consumed by tString::ReadLine without adding visible quotes."""
    return clean_console_text(value).replace("\\", "\\\\")


def readline_console_block(value: object) -> str:
    """Encode line breaks for one tString::ReadLine console command."""
    text = str(value).replace("\r\n", "\n").replace("\r", "\n")
    return text.replace("\\", "\\\\").replace("\n", "\\n")


COLOR_CODE_RE = re.compile(r"0x[0-9a-f]{6}")
INPUT_COLOR_CODE_RE = re.compile(r"0[xX][0-9a-fA-F]{6}|0[xX]RESETT")
RESOURCE_TAG_BYTES_RE = re.compile(
    br"<Resource\b[^>]*>", re.IGNORECASE | re.DOTALL
)
XML_ATTRIBUTE_BYTES_RE = re.compile(
    br"([A-Za-z_:][A-Za-z0-9_:.-]*)\s*=\s*([\"'])(.*?)\2",
    re.DOTALL,
)

# Bright, low-contrast racing palette. Armagetron renders dark color controls
# with a distracting white backing box, so every controller-owned color keeps
# at least two channels comfortably above the dark range.
COLOR_RESET = "0xffffff"
COLOR_BORDER = "0x70e6ff"
COLOR_TITLE = "0xffd166"
COLOR_RANK_HEADER = "0xff9de1"
COLOR_TIME_HEADER = "0x91ffb6"
COLOR_TURNS_HEADER = "0xc4b5ff"
COLOR_NAME_HEADER = "0xfff2a8"
COLOR_DATA = "0xe8f7ff"
COLOR_VALUE = "0xfff2a8"
COLOR_COMMAND = "0xc4b5ff"
COLOR_CHAT = "0xffff88"
COLOR_SUCCESS = "0x7dff9b"
COLOR_ERROR = "0xff8c8c"
COLOR_WARNING = "0xffc46b"
COLOR_MUTED = "0xb8c9ff"
COLOR_CURRENT_MAP = "0xff5cff"
COLOR_PLAYER_ENTERED = "0x7fff7f"
COLOR_PLAYER_LEFT = "0xff7f7f"
CHECKPOINT_CENTER_GAP = " " * 34

INLINE_COMMAND_RE = re.compile(r"(?<!\w)(/[a-z][a-z0-9_-]*)(?!\w)", re.I)
TIP_QUOTED_RE = re.compile(r'"([^"\r\n]*)"')


def normalize_console_colors(value: object) -> str:
    """Return text whose color controls use only canonical lowercase hex."""
    text = clean_console_text(value)

    def canonical(match: re.Match[str]) -> str:
        token = match.group(0)
        if token[2:].casefold() == "resett":
            return "0xffffff"
        return "0x" + token[2:].lower()

    return INPUT_COLOR_CODE_RE.sub(canonical, text)


def brighten_console_colors(value: object, minimum_channel_total: int = 500) -> str:
    """Lift user-selected dark colors while preserving their hue relationship."""
    text = normalize_console_colors(value)
    minimum_channel_total = max(0, min(765, int(minimum_channel_total)))

    def brighten(match: re.Match[str]) -> str:
        token = match.group(0)
        channels = [int(token[index:index + 2], 16) for index in (2, 4, 6)]
        total = sum(channels)
        if total >= minimum_channel_total:
            return token
        blend = (minimum_channel_total - total) / (765 - total)
        lifted = [
            min(255, round(channel + (255 - channel) * blend))
            for channel in channels
        ]
        deficit = minimum_channel_total - sum(lifted)
        for index in sorted(range(3), key=lambda item: lifted[item]):
            increase = min(deficit, 255 - lifted[index])
            lifted[index] += increase
            deficit -= increase
            if deficit <= 0:
                break
        return "0x" + "".join(f"{channel:02x}" for channel in lifted)

    return COLOR_CODE_RE.sub(brighten, text)


def plain_console_text(value: object) -> str:
    return COLOR_CODE_RE.sub("", normalize_console_colors(value))


def _message_base_color(text: str) -> str:
    """Choose a readable semantic color for an ordinary racing message."""
    lowered = text.casefold()
    if any(
        marker in lowered
        for marker in (
            "cannot",
            "disabled",
            "failed",
            "invalid",
            "no active",
            "no current",
            "no map",
            "no record",
            "not available",
            "only an owner",
            "only active",
            "rate limit",
            "unable",
            "usage:",
        )
    ):
        return COLOR_ERROR
    if any(
        marker in lowered
        for marker in (
            "already",
            "countdown",
            "please wait",
            "press brake",
            "required",
        )
    ):
        return COLOR_WARNING
    if any(
        marker in lowered
        for marker in (
            "added:",
            "enabled",
            "extended",
            "finished",
            "reloaded",
            "saved",
        )
    ):
        return COLOR_SUCCESS
    return COLOR_DATA


def _highlight_commands(text: str, base_color: str) -> str:
    return INLINE_COMMAND_RE.sub(
        lambda match: f"{COLOR_COMMAND}{match.group(1)}{base_color}",
        text,
    )


def style_console_message(value: object) -> str:
    """Apply the shared palette to every controller-owned visible message."""
    text = normalize_console_colors(value)
    if not text:
        return ""

    # Structured formatters already select their semantic colors. A base and
    # final reset still prevent user/map colors from leaking into later text.
    if COLOR_CODE_RE.search(text):
        return f"{COLOR_DATA}{text}{COLOR_RESET}"

    command_help = re.fullmatch(r"(/.+?)(\s+-\s+)(.*)", text)
    if command_help:
        command, separator, description = command_help.groups()
        return (
            f"{COLOR_COMMAND}{command}{COLOR_BORDER}{separator}"
            f"{COLOR_DATA}{description}{COLOR_RESET}"
        )

    label = re.match(r"^([^:]{1,48}:)(.*)$", text)
    if label:
        heading, remainder = label.groups()
        value_color = _message_base_color(text)
        return (
            f"{COLOR_BORDER}{heading}{value_color}"
            f"{_highlight_commands(remainder, value_color)}{COLOR_RESET}"
        )

    base_color = _message_base_color(text)
    return (
        f"{base_color}{_highlight_commands(text, base_color)}{COLOR_RESET}"
    )


def style_tip_message(value: object) -> str:
    """Render a tip in white with double-quoted contents highlighted."""
    text = plain_console_text(value)
    highlighted = TIP_QUOTED_RE.sub(
        lambda match: (
            f'"{COLOR_COMMAND}{match.group(1)}{COLOR_RESET}"'
        ),
        text,
    )
    return f"{COLOR_RESET}{highlighted}{COLOR_RESET}"


def style_console_block(lines: Iterable[object]) -> str:
    """Style each line independently, then retain their logical ordering."""
    return "\n".join(style_console_message(line) for line in lines)


def split_admin_reason(value: str) -> tuple[str, str, bool]:
    """Split `[map selector] -- [reason]` without breaking names containing dashes."""
    text = value.strip()
    separator = re.search(r"(?:^|\s)--(?:\s|$)", text)
    if not separator:
        return text, "", False
    return (
        text[: separator.start()].strip(),
        text[separator.end() :].strip(),
        True,
    )


def race_time_decimals(entry: object) -> int:
    """Return map-specific display precision without changing stored times."""
    try:
        decimals = int(getattr(entry, "time_decimals", 3))
    except (TypeError, ValueError):
        return 3
    return max(0, min(8, decimals))


def build_leaderboard_table(
    map_name: str,
    author: str,
    records: Sequence[Record],
    personal_rows: Sequence[
        tuple[str, int | str, str, float | None, int | None]
    ] = (),
    top_limit: int = 3,
    axes: int | None = None,
    rating: float | None = None,
    time_decimals: int = 3,
) -> tuple[list[str], dict[str, list[str]]]:
    """Build one common table and per-player rows that attach below it."""
    time_decimals = max(0, int(time_decimals))
    top_records = list(records[: max(0, int(top_limit))])
    top_rows: list[tuple[str, str, str, str]] = [
        (
            f"{rank}.",
            f"{record.best_seconds:.{time_decimals}f}",
            "--" if record.best_turns is None else str(record.best_turns),
            plain_console_text(record.username),
        )
        for rank, record in enumerate(top_records, 1)
    ]
    if not top_rows:
        top_rows.append(("--", "--", "--", "--"))

    top_keys = {record.identity_key for record in top_records}
    private_data: list[tuple[str, str, str, str, str]] = []
    for identity_key, rank, username, seconds, turns in personal_rows:
        if identity_key in top_keys:
            continue
        rank_text = "--" if rank == "--" else f"{rank}."
        time_text = (
            "--" if seconds is None else f"{seconds:.{time_decimals}f}"
        )
        turns_text = "--" if turns is None else str(turns)
        private_data.append(
            (
                identity_key,
                rank_text,
                time_text,
                turns_text,
                plain_console_text(username),
            )
        )

    all_rows = top_rows + [row[1:] for row in private_data]
    rank_width = max(4, *(len(row[0]) for row in all_rows))
    time_width = max(5, *(len(row[1]) for row in all_rows))
    turns_width = max(5, *(len(row[2]) for row in all_rows))
    name_width = max(12, *(min(32, len(row[3])) for row in all_rows))
    map_text = plain_console_text(f"Map: {map_name} | Author: {author}")

    # Expand the name column when the map heading needs more room.
    minimum_name_width = min(
        32,
        len(map_text) - rank_width - time_width - turns_width - 11,
    )
    name_width = max(name_width, minimum_name_width)

    def fitted(value: str, width: int) -> str:
        if len(value) <= width:
            return value
        return value[: max(0, width - 1)] + "~"

    def row(
        rank: str,
        seconds: str,
        turns: str,
        username: str,
        colors: tuple[str, str, str, str],
    ) -> str:
        rank_color, time_color, turns_color, name_color = colors
        return (
            f"{COLOR_BORDER}| {rank_color}"
            f"{fitted(rank, rank_width).center(rank_width)} {COLOR_BORDER}| "
            f"{time_color}{fitted(seconds, time_width).center(time_width)} "
            f"{COLOR_BORDER}| {turns_color}"
            f"{fitted(turns, turns_width).center(turns_width)} {COLOR_BORDER}| "
            f"{name_color}{fitted(username, name_width).center(name_width)} "
            f"{COLOR_BORDER}|{COLOR_RESET}"
        )

    column_border = (
        f"+-{'-' * rank_width}-+-{'-' * time_width}-+-{'-' * turns_width}-+"
        f"-{'-' * name_width}-+"
    )
    outer_border = "+" + "-" * (len(column_border) - 2) + "+"
    map_row = (
        f"{COLOR_BORDER}|{COLOR_TITLE}"
        f"{fitted(map_text, len(outer_border) - 2).center(len(outer_border) - 2)}"
        f"{COLOR_BORDER}|{COLOR_RESET}"
    )
    colored_outer_border = f"{COLOR_BORDER}{outer_border}{COLOR_RESET}"
    colored_column_border = f"{COLOR_BORDER}{column_border}{COLOR_RESET}"
    axes_value = "--" if axes is None else str(axes)
    rating_value = "--/5" if rating is None else f"{rating:.2f}/5"
    status_left_width = rank_width + time_width + 3
    status_right_width = turns_width + name_width + 3
    status_border = (
        f"+-{'-' * status_left_width}-+-{'-' * status_right_width}-+"
    )
    colored_status_border = f"{COLOR_BORDER}{status_border}{COLOR_RESET}"

    def centered_status_cell(
        label: str,
        value: str,
        width: int,
        label_color: str,
    ) -> str:
        visible = f"{label}: {value}"
        remaining = max(0, width - len(visible))
        left = remaining // 2
        right = remaining - left
        return (
            f"{' ' * left}{label_color}{label}: {COLOR_VALUE}{value}"
            f"{' ' * right}"
        )

    status_row = (
        f"{COLOR_BORDER}| "
        f"{centered_status_cell('Axes', axes_value, status_left_width, COLOR_RANK_HEADER)}"
        f" {COLOR_BORDER}| "
        f"{centered_status_cell('Rating', rating_value, status_right_width, COLOR_TIME_HEADER)} "
        f"{COLOR_BORDER}|{COLOR_RESET}"
    )
    header_colors = (
        COLOR_RANK_HEADER,
        COLOR_TIME_HEADER,
        COLOR_TURNS_HEADER,
        COLOR_NAME_HEADER,
    )
    data_colors = (COLOR_DATA, COLOR_DATA, COLOR_DATA, COLOR_DATA)
    common = [
        colored_outer_border,
        map_row,
        colored_column_border,
        row("Rank", "Time", "Turns", "Name", header_colors),
        colored_column_border,
        *(row(*values, data_colors) for values in top_rows),
        colored_column_border,
        status_row,
        colored_status_border,
    ]
    private = {
        identity_key: [
            row(rank, seconds, turns, username, data_colors),
            colored_column_border,
        ]
        for identity_key, rank, seconds, turns, username in private_data
    }
    return common, private


def format_finish_message(
    colored_username: str,
    seconds: float,
    finish_rank: int,
    best_seconds: float,
    best_rank: int,
    previous_best: float | None,
    turns: int | None,
    best_turns: int | None,
    previous_best_turns: int | None,
    no_cp_seconds: float | None = None,
    no_cp_rank: int | None = None,
    no_cp_turns: int | None = None,
    improved: bool = False,
    previous_best_rank: int | None = None,
    time_decimals: int = 3,
) -> str:
    time_decimals = max(0, int(time_decimals))
    colored_username = brighten_console_colors(colored_username)
    turns_text = "--" if turns is None else str(turns)
    finish_text = (
        f"{colored_username}{COLOR_RESET} {COLOR_BORDER}- "
        f"{COLOR_TIME_HEADER}Finish: {COLOR_VALUE}"
        f"{seconds:.{time_decimals}f}"
        f"{COLOR_MUTED}, {COLOR_TURNS_HEADER}Turns: {COLOR_VALUE}{turns_text}"
        f"{COLOR_MUTED}, {COLOR_RANK_HEADER}Rank: {COLOR_VALUE}{finish_rank}"
        f"{COLOR_RESET}"
    )
    if previous_best is None and no_cp_seconds is None:
        return finish_text

    reference = previous_best if previous_best is not None else best_seconds
    split = round(seconds - reference, time_decimals)
    if split < 0:
        color = COLOR_SUCCESS
        split_text = f"{split:.{time_decimals}f}"
    elif split > 0:
        color = COLOR_ERROR
        split_text = f"+{split:.{time_decimals}f}"
    else:
        color = COLOR_MUTED
        split_text = f"{0:.{time_decimals}f}"

    turn_reference = (
        best_turns if previous_best is None else previous_best_turns
    )
    if turns is None or turn_reference is None:
        turn_color = COLOR_MUTED
        turn_split_text = "--"
    else:
        turn_split = turns - turn_reference
        if turn_split < 0:
            turn_color = COLOR_SUCCESS
            turn_split_text = str(turn_split)
        elif turn_split > 0:
            turn_color = COLOR_ERROR
            turn_split_text = f"+{turn_split}"
        else:
            turn_color = COLOR_MUTED
            turn_split_text = "0"

    show_previous_best = improved and previous_best is not None
    reference_label = "Previous best" if show_previous_best else "Best"
    displayed_best = previous_best if show_previous_best else best_seconds
    displayed_turns = previous_best_turns if show_previous_best else best_turns
    displayed_rank = (
        previous_best_rank
        if show_previous_best and previous_best_rank is not None
        else best_rank
    )
    best_turns_text = "--" if displayed_turns is None else str(displayed_turns)
    message = (
        f"{finish_text} {COLOR_BORDER}| {COLOR_TIME_HEADER}{reference_label}: "
        f"{COLOR_VALUE}{displayed_best:.{time_decimals}f}{COLOR_MUTED}, "
        f"{COLOR_TURNS_HEADER}Turns: {COLOR_VALUE}{best_turns_text}"
        f"{COLOR_MUTED}, {COLOR_RANK_HEADER}Rank: {COLOR_VALUE}{displayed_rank} "
        f"{COLOR_BORDER}| {COLOR_NAME_HEADER}Split: {color}{split_text}"
        f"{COLOR_MUTED}, {turn_color}{turn_split_text}{COLOR_RESET}"
    )
    if no_cp_seconds is None:
        return message

    no_cp_turns_text = "--" if no_cp_turns is None else str(no_cp_turns)
    no_cp_rank_text = "--" if no_cp_rank is None else str(no_cp_rank)
    no_cp_split = round(no_cp_seconds - best_seconds, time_decimals)
    if no_cp_split < 0:
        no_cp_split_color = COLOR_SUCCESS
        no_cp_split_text = f"{no_cp_split:.{time_decimals}f}"
    elif no_cp_split > 0:
        no_cp_split_color = COLOR_ERROR
        no_cp_split_text = f"+{no_cp_split:.{time_decimals}f}"
    else:
        no_cp_split_color = COLOR_MUTED
        no_cp_split_text = f"{0:.{time_decimals}f}"
    if no_cp_turns is None or best_turns is None:
        no_cp_turn_color = COLOR_MUTED
        no_cp_turn_split_text = "--"
    else:
        no_cp_turn_split = no_cp_turns - best_turns
        if no_cp_turn_split < 0:
            no_cp_turn_color = COLOR_SUCCESS
            no_cp_turn_split_text = str(no_cp_turn_split)
        elif no_cp_turn_split > 0:
            no_cp_turn_color = COLOR_ERROR
            no_cp_turn_split_text = f"+{no_cp_turn_split}"
        else:
            no_cp_turn_color = COLOR_MUTED
            no_cp_turn_split_text = "0"
    return (
        f"{message} {COLOR_BORDER}| {COLOR_TIME_HEADER}No-CP: "
        f"{COLOR_VALUE}{no_cp_seconds:.{time_decimals}f}{COLOR_MUTED}, "
        f"{COLOR_RANK_HEADER}Rank: {COLOR_VALUE}{no_cp_rank_text}"
        f"{COLOR_MUTED}, {COLOR_TURNS_HEADER}Turns: "
        f"{COLOR_VALUE}{no_cp_turns_text} {COLOR_BORDER}| "
        f"{COLOR_NAME_HEADER}Split: {no_cp_split_color}{no_cp_split_text}"
        f"{COLOR_MUTED}, {no_cp_turn_color}{no_cp_turn_split_text}"
        f"{COLOR_RESET}"
    )


def bump_resource_version(version: str) -> str:
    match = re.match(r"^(.*?)(\d+)$", version)
    if not match:
        return version + ".1"
    prefix, digits = match.groups()
    bumped = str(int(digits) + 1)
    if len(digits) > 1 and digits.startswith("0"):
        bumped = bumped.zfill(len(digits))
    return prefix + bumped


def rewrite_map_resource_version(data: bytes, version: str) -> bytes:
    """Change only the Resource version attribute, preserving all other bytes."""
    resource = RESOURCE_TAG_BYTES_RE.search(data)
    if resource is None:
        raise ValueError("map has no Resource tag")
    tag = resource.group(0)
    version_attribute = next(
        (
            match
            for match in XML_ATTRIBUTE_BYTES_RE.finditer(tag)
            if match.group(1).lower() == b"version"
        ),
        None,
    )
    if version_attribute is None:
        raise ValueError("map Resource tag has no version attribute")
    updated_tag = (
        tag[:version_attribute.start(3)]
        + version.encode("utf-8")
        + tag[version_attribute.end(3):]
    )
    return data[:resource.start()] + updated_tag + data[resource.end():]


def install_immutable_file(source: Path, destination: Path) -> None:
    """Install a file once, refusing to change bytes at an existing path."""
    data = source.read_bytes()
    if destination.exists():
        if destination.read_bytes() != data:
            raise RuntimeError(
                f"immutable resource conflict at {destination}"
            )
        return
    destination.parent.mkdir(parents=True, exist_ok=True)
    temporary = destination.with_name(
        f".{destination.name}.{os.getpid()}.tmp"
    )
    try:
        with temporary.open("xb") as handle:
            handle.write(data)
            handle.flush()
            os.fsync(handle.fileno())
        os.chmod(temporary, 0o644)
        os.replace(temporary, destination)
    finally:
        with contextlib.suppress(FileNotFoundError):
            temporary.unlink()


def format_size_factor(value: float) -> str:
    if abs(value) < 0.0000005:
        value = 0.0
    return f"{value:.6f}".rstrip("0").rstrip(".")


def padded_center_command(value: object, padding: int = 10) -> str:
    # ReadLine strips ordinary leading whitespace. Each escaped space survives
    # parsing as one actual leading space; trailing spaces already survive.
    left = "\\ " * padding
    right = " " * padding
    text = readline_console_text(style_console_message(value))
    return f"CENTER_MESSAGE {left}{text}{right}"


def server_restart_center_command(seconds: int) -> str:
    return f"CENTER_MESSAGE 0xff0000{int(seconds)}{' ' * 24}0xffffff "


def final_countdown_center_command(seconds: int, highest: int) -> str:
    """Render a left-offset countdown fading green through yellow to red."""
    number = max(0, int(seconds))
    maximum = max(1, int(highest))
    if maximum == 1:
        progress = 0.0 if number >= maximum else 1.0
    else:
        progress = max(
            0.0,
            min(1.0, (maximum - min(number, maximum)) / (maximum - 1)),
        )
    if progress <= 0.5:
        red = round(510 * progress)
        green = 255
    else:
        red = 255
        green = round(510 * (1.0 - progress))
    color = f"0x{red:02x}{green:02x}00"
    return (
        f"CENTER_MESSAGE {color}{number}"
        f"{' ' * FINAL_COUNTDOWN_CENTER_PADDING}0xffffff "
    )


def normalized_map_name(value: str) -> str:
    value = unicodedata.normalize("NFKC", value).casefold()
    return "".join(ch for ch in value if ch.isalnum())


def parse_intercepted_command(payload: str) -> tuple[str, str, int, str] | None:
    """Return command, player log name, access level, and argument tail."""
    parts = payload.split(maxsplit=4)
    if len(parts) < 4:
        return None
    try:
        access_level = int(parts[3])
    except ValueError:
        return None
    return (
        parts[0].casefold(),
        parts[1],
        access_level,
        parts[4].strip() if len(parts) > 4 else "",
    )


def extend_votes_required(active_players: int) -> int:
    return 1 if active_players <= 1 else math.ceil(0.60 * active_players)


def skip_votes_required(active_players: int) -> int:
    return math.floor(0.60 * max(1, active_players)) + 1


def final_countdown_seconds(records: Sequence[Record]) -> float:
    return records[0].best_seconds * 1.5 if records else 90.0


def format_final_countdown_rating_message(
    rating_summary: tuple[float, int] | None,
) -> str:
    rating_text = (
        f"Current rating: {rating_summary[0]:.1f}/5 "
        f"({rating_summary[1]} "
        f"{'rating' if rating_summary[1] == 1 else 'ratings'})."
        if rating_summary
        else "Current rating: unrated."
    )
    return (
        f"{COLOR_TITLE}{rating_text}{COLOR_RESET} "
        f"Use {COLOR_COMMAND}/rate #{COLOR_RESET} for the current map or "
        f"{COLOR_COMMAND}/rate [map] #{COLOR_RESET} for a specific map."
    )


def map_play_seconds(
    records: Sequence[Record],
    maximum_seconds: float = 300.0,
    racer_time_multiplier: float = 1.25,
    target_finishes: float = 5.0,
    minimum_seconds: float = 120.0,
) -> float:
    """Return the adaptive map window, bounded by its minimum and maximum."""
    minimum = max(0.0, float(minimum_seconds))
    maximum = max(minimum, float(maximum_seconds))
    if not records:
        return maximum
    best = float(records[0].best_seconds)
    multiplier = max(0.0, float(racer_time_multiplier))
    finishes = max(0.0, float(target_finishes))
    calculated = best * multiplier * finishes
    if not math.isfinite(calculated) or calculated <= 0:
        return maximum
    return max(minimum, min(maximum, calculated))


def map_open_play_seconds(
    records: Sequence[Record],
    maximum_seconds: float = 300.0,
    racer_time_multiplier: float = 1.25,
    target_finishes: float = 5.0,
    minimum_seconds: float = 120.0,
) -> float:
    """Return the full respawn-enabled window before the final countdown."""
    return map_play_seconds(
        records,
        maximum_seconds,
        racer_time_multiplier,
        target_finishes,
        minimum_seconds,
    )


def parse_winzone_finish(payload: str) -> tuple[str, float, int | None] | None:
    """Parse the sty+ct+ap WINZONE_PLAYER_ENTER format actually emitted.

    The optional zone name may be empty; indexing from the right keeps the
    player and game-time fields stable in both forms.
    """
    parts = payload.split()
    if len(parts) < 6:
        return None
    try:
        finish_time = float(parts[-1])
    except ValueError:
        return None
    if parts[-2].startswith("turns="):
        try:
            return parts[-7], finish_time, int(parts[-2][len("turns="):])
        except (ValueError, IndexError):
            return None
    try:
        return parts[-6], finish_time, None
    except IndexError:
        return None


@dataclasses.dataclass(frozen=True)
class CheckpointEntry:
    player_name: str
    checkpoint_id: int
    game_time: float
    x: float | None = None
    y: float | None = None
    xdir: float | None = None
    ydir: float | None = None
    speed: float | None = None
    turns: int | None = None

    @property
    def has_respawn_state(self) -> bool:
        return None not in (
            self.x,
            self.y,
            self.xdir,
            self.ydir,
            self.speed,
            self.turns,
        )


def parse_checkpoint_entry(payload: str) -> CheckpointEntry | None:
    """Parse legacy or checkpoint-respawn CHECKPOINT_PLAYER_ENTER events."""
    parts = payload.split()
    if len(parts) not in {3, 9}:
        return None
    try:
        checkpoint_id = int(parts[1])
        if len(parts) == 3:
            game_time = float(parts[2])
            state: tuple[float, float, float, float, float, int] | None = None
        else:
            state = (
                float(parts[2]),
                float(parts[3]),
                float(parts[4]),
                float(parts[5]),
                float(parts[6]),
                int(parts[7]),
            )
            game_time = float(parts[8])
    except ValueError:
        return None
    if checkpoint_id <= 0 or not math.isfinite(game_time):
        return None
    if state is None:
        return CheckpointEntry(parts[0], checkpoint_id, game_time)
    x, y, xdir, ydir, speed, turns = state
    if (
        not all(math.isfinite(value) for value in (x, y, xdir, ydir, speed))
        or speed < 0
        or turns < 0
        or turns > 65535
        or (xdir == 0 and ydir == 0)
    ):
        return None
    return CheckpointEntry(
        parts[0], checkpoint_id, game_time, x, y, xdir, ydir, speed, turns
    )


def safe_resource_component(value: str) -> bool:
    if not value or value in {".", ".."}:
        return False
    return not any(ch in value for ch in "/\\();\r\n\t") and not any(
        ch.isspace() for ch in value
    )


def load_json_object(path: Path) -> dict:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
        return value if isinstance(value, dict) else {}
    except (OSError, json.JSONDecodeError):
        return {}


def load_helpful_messages(path: Path) -> list[str]:
    """Load one console message per nonempty, non-comment line."""
    try:
        lines = path.read_text(encoding="utf-8").splitlines()
    except OSError:
        return []
    return [
        clean_console_text(line)
        for line in lines
        if line.strip() and not line.lstrip().startswith("#")
    ]


def load_custom_helpful_messages(store: "StateStore") -> list[str]:
    """Return valid admin-created tips in their stable ID order."""
    state = store.get_json("custom_helpful_messages", {})
    tips = state.get("tips", []) if isinstance(state, dict) else []
    if not isinstance(tips, list):
        return []
    valid: list[tuple[int, str]] = []
    for item in tips:
        if not isinstance(item, dict):
            continue
        try:
            tip_id = int(item.get("id"))
        except (TypeError, ValueError):
            continue
        message = clean_console_text(item.get("message", ""))
        if tip_id > 0 and message:
            valid.append((tip_id, message))
    return [message for _, message in sorted(valid)]


def atomic_write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(f".{path.name}.{os.getpid()}.tmp")
    with temporary.open("w", encoding="utf-8") as handle:
        json.dump(value, handle, ensure_ascii=False, indent=2, sort_keys=True)
        handle.write("\n")
        handle.flush()
        os.fsync(handle.fileno())
    os.chmod(temporary, 0o600)
    os.replace(temporary, path)


def atomic_write_text(path: Path, value: str) -> None:
    """Write one private controller-to-engine artifact atomically."""
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(f".{path.name}.{os.getpid()}.tmp")
    with temporary.open("w", encoding="ascii", newline="\n") as handle:
        handle.write(value)
        if not value.endswith("\n"):
            handle.write("\n")
        handle.flush()
        os.fsync(handle.fileno())
    os.chmod(temporary, 0o600)
    os.replace(temporary, path)


def send_resend_report(
    api_key: str,
    recipient: str,
    sender: str,
    subject: str,
    body: str,
    endpoint: str = RESEND_ENDPOINT,
    timeout_seconds: float = 10.0,
) -> None:
    """Send one complete report without exposing its API key in logs or argv."""
    request_body = json.dumps(
        {
            "from": sender,
            "to": [recipient],
            "subject": subject,
            "text": body,
        },
        ensure_ascii=False,
    ).encode("utf-8")
    request = urllib.request.Request(
        endpoint,
        data=request_body,
        headers={
            "Accept": "application/json",
            "Authorization": f"Bearer {api_key}",
            "Content-Type": "application/json",
            "User-Agent": "TronnerRacing/1.0",
        },
        method="POST",
    )
    try:
        with urllib.request.urlopen(request, timeout=timeout_seconds) as response:
            status = response.getcode()
            response_body = response.read(16384)
    except urllib.error.HTTPError as error:
        status = error.code
        response_body = error.read(16384)
    if not 200 <= status < 300:
        raise RuntimeError(f"report service returned HTTP {status}")
    try:
        result = json.loads(response_body.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise RuntimeError("report service returned an invalid response") from error
    if not isinstance(result, dict) or not result.get("id"):
        raise RuntimeError("report service rejected the submission")


class GameLinkServiceError(RuntimeError):
    """A safe error returned by the website's one-time link endpoint."""

    def __init__(self, code: str, public_message: str):
        super().__init__(public_message)
        self.code = code
        self.public_message = public_message


def redeem_game_account_link(
    endpoint: str,
    secret: str,
    code: str,
    game_username: str,
    server_id: str,
    timeout_seconds: float = 10.0,
) -> dict[str, object]:
    """Redeem a short-lived website code for a server-authenticated global id."""
    parsed_endpoint = urllib.parse.urlsplit(endpoint)
    if parsed_endpoint.scheme != "https" or not parsed_endpoint.hostname:
        raise RuntimeError("game link endpoint must be HTTPS")
    request_body = json.dumps(
        {
            "code": code,
            "gameUsername": game_username,
            "serverId": server_id,
        },
        ensure_ascii=False,
        allow_nan=False,
        separators=(",", ":"),
    ).encode("utf-8")
    request = urllib.request.Request(
        endpoint,
        data=request_body,
        headers={
            "Accept": "application/json",
            "Authorization": f"Bearer {secret}",
            "Content-Type": "application/json",
            "User-Agent": "TronnerRacing/1.0",
        },
        method="POST",
    )
    try:
        with urllib.request.urlopen(request, timeout=timeout_seconds) as response:
            status = response.getcode()
            response_body = response.read(16_384)
    except urllib.error.HTTPError as error:
        status = error.code
        try:
            response_body = error.read(16_384)
        finally:
            error.close()
    try:
        result = json.loads(response_body.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise RuntimeError("game link service returned an invalid response") from error
    if not 200 <= status < 300:
        details = result.get("error", {}) if isinstance(result, dict) else {}
        error_code = str(details.get("code", "link-failed"))[:80]
        public_message = str(
            details.get("message", "Unable to link that account right now.")
        ).strip()[:240]
        raise GameLinkServiceError(
            error_code,
            public_message or "Unable to link that account right now.",
        )
    if not isinstance(result, dict) or result.get("linked") is not True:
        raise RuntimeError("game link service rejected the claim")
    return result


USER_COMMAND_HELP = (
    ("/q add [map name]", "Queue a map after the current map."),
    ("/q lowest", "Queue your lowest-ranked or an unranked map."),
    ("/q remove [map]", "Remove the first matching map from the queue."),
    ("/q clear", "Clear every map from the queue."),
    ("/rate [1-5]", "Rate the current map."),
    ("/rate [map] [1-5]", "Rate a specific map."),
    ("/rate undo", "Undo your latest rating change on the current map."),
    ("/rate revoke", "Remove your rating from the current map."),
    ("/extend", "Vote to add five minutes to the current map."),
    ("/skip", "Vote to advance to the next map."),
    ("/nextmap", "Show the next queued or rotated map."),
    ("/rotation", "Privately show the alphabetical map rotation."),
    ("/exclusion_list", "Privately show maps excluded from rotation."),
    ("/leaderboard", "Privately show the current map's top 10 times."),
    ("/results", "Toggle finish and rank messages."),
    (
        "/ghost [pb|wr|rank #|player name|off]",
        "Race a private replay ghost on your next attempt.",
    ),
    (
        "/setspawn [#]",
        "Always use a spawn number; omit # for latest or use 0 to clear it.",
    ),
    (
        "/start [brake|immediate|countdown|respawn] [respawn seconds]",
        "Choose how your cycle begins moving and optionally set its respawn wait.",
    ),
    (
        "/practice [reset|maintain] [seconds]",
        "Practice this map; rewind after death without recording times.",
    ),
    ("/practice off", "Disable practice mode."),
    (
        "/link [6-digit code]",
        "Link your authenticated in-game name to your tronner.io account.",
    ),
    (
        "/cp",
        "Respawn from your last checkpoint; a quick second /cp resets speed.",
    ),
    ("/restart", "Clear checkpoint progress and restart from the map spawn."),
    ("/respawn", "Kill your current cycle and respawn at your last checkpoint."),
    ("/sui", "Same as /respawn: kill your cycle and enable respawning."),
    ("/join", "Enable respawning without killing your current cycle."),
    ("/spec or /spectate", "Disable scripted respawning."),
    ("/report [message]", "Privately send a report to the server owner."),
    ("/suggest [message]", "Privately suggest a feature to the server owner."),
    ("/help [search term]", "Show or search the commands available to you."),
)

ADMIN_COMMAND_HELP = (
    ("records_admin_access_level", "/forceskip", "Advance without a vote."),
    ("map_admin_access_level", "/end", "Start the end-of-map timer."),
    (
        "records_admin_access_level",
        "/resetalltimes",
        "Delete every time on the current map.",
    ),
    (
        "records_admin_access_level",
        "/reset [user] [map]",
        "Delete one user's time; map defaults to current.",
    ),
    (
        "records_admin_access_level",
        "/message [player] [message]",
        "Save a private message for a player's next authenticated login.",
    ),
    (
        "map_admin_access_level",
        "/exclude [map] -- [reason]",
        "Hold a map out of rotation; map and reason are optional.",
    ),
    (
        "map_admin_access_level",
        "/review [map] -- [reason]",
        "Send a map and optional reason to Vectron; also supports list/remove.",
    ),
    (
        "map_admin_access_level",
        "/remove_exclusion [map]",
        "Return an excluded map to the pool.",
    ),
    ("map_admin_access_level", "/reloadmaps", "Reload maps from the repository."),
    ("size_admin_access_level", "/size [+x|-x]", "Change this map's size factor."),
)


def build_help_lines(entries: Sequence[tuple[str, str]]) -> list[str]:
    """Format command help as two left-aligned, consistently spaced columns."""
    visible_entries = [
        (plain_console_text(command), plain_console_text(description))
        for command, description in entries
    ]
    if not visible_entries:
        return []
    command_width = max(len(command) for command, _ in visible_entries)
    return [
        f"{command.ljust(command_width)} - {description}"
        for command, description in visible_entries
    ]


def search_help_entries(
    entries: Sequence[tuple[str, str]], query: object
) -> list[tuple[str, str]]:
    """Return case-insensitive help matches, preferring an exact command name."""
    needle = " ".join(plain_console_text(query).split()).casefold()
    if not needle:
        return list(entries)
    command_name = needle.removeprefix("/")
    exact_command_matches = [
        (command, description)
        for command, description in entries
        if plain_console_text(command)
        .lstrip("/")
        .split(maxsplit=1)[0]
        .casefold()
        == command_name
    ]
    if exact_command_matches:
        return exact_command_matches
    matches = []
    for command, description in entries:
        haystack = (
            f"{plain_console_text(command)} {plain_console_text(description)}"
        ).casefold()
        if needle in haystack:
            matches.append((command, description))
    return matches


def build_compact_columns(
    items: Sequence[str],
    column_count: int = 4,
    gap: str = "  ",
) -> list[str]:
    """Pack sorted items top-to-bottom into compact, aligned columns."""
    raw_items = [str(item) for item in items]
    visible_items = [plain_console_text(item) for item in raw_items]
    if not visible_items or column_count <= 0:
        return []

    active_columns = min(column_count, len(visible_items))
    base_size, extra = divmod(len(visible_items), active_columns)
    sizes = [base_size + (index < extra) for index in range(active_columns)]
    columns: list[list[tuple[str, str]]] = []
    offset = 0
    for size in sizes:
        columns.append(
            list(
                zip(
                    raw_items[offset:offset + size],
                    visible_items[offset:offset + size],
                )
            )
        )
        offset += size
    widths = [max(len(visible) for _, visible in column) for column in columns]

    lines = []
    for row_index in range(max(sizes)):
        last_column = max(
            index
            for index, column in enumerate(columns)
            if row_index < len(column)
        )
        cells = []
        for column_index in range(last_column + 1):
            column = columns[column_index]
            if row_index < len(column):
                value, visible = column[row_index]
            else:
                value, visible = "", ""
            if column_index < last_column:
                value += " " * (widths[column_index] - len(visible))
            cells.append(value)
        lines.append(gap.join(cells))
    return lines


def build_rotation_columns(
    items: Sequence[tuple[str, str, str, bool]],
    column_count: int = 2,
    field_gap: str = "  ",
    column_gap: str = "   |   ",
) -> list[str]:
    """Build map blocks containing aligned name, author, and version fields."""
    raw_items = [
        (str(name), str(author), str(version), bool(is_current))
        for name, author, version, is_current in items
    ]
    if not raw_items or column_count <= 0:
        return []

    active_columns = min(column_count, len(raw_items))
    base_size, extra = divmod(len(raw_items), active_columns)
    sizes = [base_size + (index < extra) for index in range(active_columns)]
    columns: list[list[tuple[str, str, str, bool]]] = []
    offset = 0
    for size in sizes:
        columns.append(raw_items[offset:offset + size])
        offset += size

    headings = ("Map name", "Author", "Version")
    widths = []
    for column in columns:
        widths.append(
            tuple(
                max(
                    len(headings[field_index]),
                    *(
                        len(plain_console_text(item[field_index]))
                        for item in column
                    ),
                )
                for field_index in range(3)
            )
        )

    def format_block(
        values: tuple[str, str, str],
        block_widths: tuple[int, int, int],
    ) -> str:
        fields = []
        for field_index, value in enumerate(values):
            visible_width = len(plain_console_text(value))
            padding = block_widths[field_index] - visible_width
            fields.append(value + (" " * padding))
        return field_gap.join(fields)

    lines = [
        column_gap.join(
            format_block(headings, block_widths)
            for block_widths in widths
        )
    ]
    for row_index in range(max(sizes)):
        last_column = max(
            index
            for index, column in enumerate(columns)
            if row_index < len(column)
        )
        blocks = []
        for column_index in range(last_column + 1):
            column = columns[column_index]
            block_widths = widths[column_index]
            if row_index < len(column):
                name, author, version, is_current = column[row_index]
                block = format_block((name, author, version), block_widths)
                if is_current:
                    block = f"{COLOR_CURRENT_MAP}{block}{COLOR_RESET}"
            else:
                block = " " * (
                    sum(block_widths) + (len(field_gap) * 2)
                )
            blocks.append(block)
        lines.append(column_gap.join(blocks).rstrip())
    return lines


@dataclasses.dataclass(frozen=True)
class SpawnPoint:
    x: float
    y: float
    xdir: float
    ydir: float


@dataclasses.dataclass(frozen=True)
class MapEntry:
    key: str
    name: str
    author: str
    version: str
    category: str
    source_path: str
    local_path: Path
    spawns: tuple[SpawnPoint, ...]
    axes: int | None = None
    map_id: str = ""
    revision_id: str = ""
    storage_path: str = ""
    record_key: str = ""
    rating_key_override: str = ""
    checkpoint_ids: tuple[int, ...] = ()
    checkpoint_mode: str = ""
    time_decimals: int = 3

    @property
    def label(self) -> str:
        return f"{self.name} by {self.author}"

    @property
    def rating_key(self) -> str:
        """Stable logical identity shared by resource/size revisions."""
        if self.rating_key_override:
            return self.rating_key_override
        parts = [self.author, *self.category.split("/"), self.name]
        return "/".join(part for part in parts if part).casefold()

    @property
    def records_key(self) -> str:
        """Revision identity used by finish records and leaderboards."""
        return self.record_key or self.key


def map_records_key(entry: object) -> str:
    """Return a record identity while supporting lightweight test doubles."""
    return str(getattr(entry, "records_key", getattr(entry, "key")))


def map_spawn_preferences_key(entry: object) -> str:
    """Return a stable map identity that survives published revisions."""
    map_id = str(getattr(entry, "map_id", "")).strip()
    if map_id:
        return f"map-id:{map_id}"
    rating_key = str(getattr(entry, "rating_key", "")).strip().casefold()
    if rating_key:
        return f"logical:{rating_key}"
    return f"resource:{getattr(entry, 'key')}"


def _encode_unsigned_varint(value: int) -> bytes:
    if value < 0:
        raise ValueError("varint value must be nonnegative")
    encoded = bytearray()
    while value >= 0x80:
        encoded.append((value & 0x7F) | 0x80)
        value >>= 7
    encoded.append(value)
    return bytes(encoded)


def encode_replay_inputs(events: Iterable[tuple[int, int]]) -> bytes:
    """Pack signed microsecond deltas and two-bit actions into varints."""
    encoded = bytearray()
    previous_offset = 0
    for offset_us, action in events:
        if action < 0 or action > 3:
            raise ValueError("replay action must fit in two bits")
        delta = int(offset_us) - previous_offset
        previous_offset = int(offset_us)
        zigzag = (delta << 1) if delta >= 0 else ((-delta << 1) - 1)
        encoded.extend(_encode_unsigned_varint((zigzag << 2) | action))
    return bytes(encoded)


def decode_replay_inputs(data: bytes) -> list[tuple[int, int]]:
    """Decode a version-one replay input stream for validation/playback."""
    events: list[tuple[int, int]] = []
    value = 0
    shift = 0
    offset = 0
    for byte in data:
        value |= (byte & 0x7F) << shift
        if byte & 0x80:
            shift += 7
            if shift > 63:
                raise ValueError("replay varint is too large")
            continue
        action = value & 3
        zigzag = value >> 2
        delta = -(zigzag // 2) - 1 if zigzag & 1 else zigzag // 2
        offset += delta
        events.append((offset, action))
        value = 0
        shift = 0
    if shift:
        raise ValueError("truncated replay varint")
    return events


def encode_replay_settings(items: Iterable[tuple[bytes, bytes]]) -> bytes:
    """Encode a deterministic, lossless settings snapshot before compression."""
    values = list(items)
    encoded = bytearray(b"TRS\x01")
    encoded.extend(_encode_unsigned_varint(len(values)))
    for name, value in values:
        encoded.extend(_encode_unsigned_varint(len(name)))
        encoded.extend(name)
        encoded.extend(_encode_unsigned_varint(len(value)))
        encoded.extend(value)
    return bytes(encoded)


def _decode_unsigned_varint(data: bytes, offset: int) -> tuple[int, int]:
    value = 0
    shift = 0
    while offset < len(data):
        byte = data[offset]
        offset += 1
        value |= (byte & 0x7F) << shift
        if not byte & 0x80:
            return value, offset
        shift += 7
        if shift > 63:
            raise ValueError("settings varint is too large")
    raise ValueError("truncated settings varint")


def decode_replay_settings(data: bytes) -> list[tuple[bytes, bytes]]:
    """Decode the uncompressed version-one settings snapshot format."""
    if not data.startswith(b"TRS\x01"):
        raise ValueError("unsupported replay settings format")
    offset = 4
    count, offset = _decode_unsigned_varint(data, offset)
    items: list[tuple[bytes, bytes]] = []
    for _ in range(count):
        name_length, offset = _decode_unsigned_varint(data, offset)
        name_end = offset + name_length
        if name_end > len(data):
            raise ValueError("truncated replay setting name")
        name = data[offset:name_end]
        offset = name_end
        value_length, offset = _decode_unsigned_varint(data, offset)
        value_end = offset + value_length
        if value_end > len(data):
            raise ValueError("truncated replay setting value")
        items.append((name, data[offset:value_end]))
        offset = value_end
    if offset != len(data):
        raise ValueError("trailing replay settings data")
    return items


def publish_repository_map_status(
    repository: object,
    key: str,
    status: str,
    reason: str,
) -> None:
    """Publish status when the repository backend supports mutations."""
    setter = getattr(repository, "set_map_status", None)
    if callable(setter):
        setter(key, status, reason)


@dataclasses.dataclass(frozen=True)
class CheckpointSnapshot:
    checkpoint_id: int
    x: float
    y: float
    xdir: float
    ydir: float
    speed: float
    turns: int
    event_game: float
    attempt_started_game: float
    checkpoints_collected: frozenset[int]
    no_cp_elapsed: float


@dataclasses.dataclass(frozen=True)
class PracticeSnapshot:
    game_time: float
    x: float
    y: float
    xdir: float
    ydir: float
    speed: float
    turns: int


@dataclasses.dataclass
class Player:
    log_name: str
    display_name: str
    auth_name: str | None = None
    colored_name: str | None = None
    color_code: str | None = None
    connection_address: str = ""
    ip_address: str = ""
    owner_id: int | None = None
    connected: bool = True
    active: bool = True
    forced_racing: bool = False
    alive: bool = False
    spawn_cursor: int = 0
    last_spawn_index: int | None = None
    generation: int = 0
    pending_respawn: bool = False
    respawn_created_game: float | None = None
    attempt_started_game: float | None = None
    attempt_number: int = 0
    respawn_enabled: bool = True
    is_ai: bool = False
    last_turn_monotonic: float | None = None
    afk: bool = False
    activity_snapshot_seen: bool = False
    suspended_votes: dict[str, int] = dataclasses.field(default_factory=dict)
    start_mode: str = "immediate"
    start_respawn_delay_seconds: float = DEFAULT_START_RESPAWN_DELAY_SECONDS
    pending_start_mode: str = "immediate"
    manual_restart_pending: bool = False
    checkpoints_collected: set[int] = dataclasses.field(default_factory=set)
    checkpoint_notice_monotonic: float | None = None
    checkpoint_snapshot: CheckpointSnapshot | None = None
    checkpoint_respawn_requested: bool = False
    checkpoint_respawn_speed: float | None = None
    checkpoint_respawn_used: bool = False
    pending_respawn_kind: str = ""
    no_cp_elapsed: float = 0.0
    no_cp_segment_started_game: float | None = None
    last_checkpoint_respawn_monotonic: float | None = None
    last_checkpoint_game: float | None = None
    practice_mode: str = "off"
    practice_rewind_seconds: float = 0.0
    practice_map_key: str = ""
    practice_samples: collections.deque[PracticeSnapshot] = dataclasses.field(
        default_factory=collections.deque
    )
    practice_respawn_snapshot: PracticeSnapshot | None = None
    practice_start_respawn_pending: bool = False
    practice_finish_pending: bool = False
    practice_attempt_tainted: bool = False
    cycle_xdir: float = 1.0
    cycle_ydir: float = 0.0
    cycle_speed: float = 0.0
    cycle_turns: int = 0

    @property
    def target(self) -> str:
        return self.log_name

    @property
    def record_name(self) -> str:
        return self.auth_name or self.display_name or self.log_name

    @property
    def identity_key(self) -> str:
        if self.auth_name:
            return "auth:" + self.auth_name.casefold()
        return "guest:" + self.record_name.casefold()

    @property
    def colored_display_name(self) -> str:
        if self.colored_name:
            return brighten_console_colors(self.colored_name)
        color = brighten_console_colors(self.color_code or COLOR_RESET)
        return f"{color}{self.display_name or self.log_name}"


@dataclasses.dataclass(frozen=True)
class ReplayEventState:
    x: float
    y: float
    xdir: float
    ydir: float
    speed: float
    turns: int


@dataclasses.dataclass
class ReplayCapture:
    token: str
    player_log_name: str
    identity_key: str
    username: str
    authenticated: bool
    map_identifier: str
    revision_identifier: str
    resource_key: str
    started_at: float
    spawn_game_time: float
    x: float
    y: float
    xdir: float
    ydir: float
    speed: float
    initial_turns: int
    size_factor: float | None
    start_mode: str
    checkpoint_spawn: bool
    initial_distance: float = 0.0
    latest_distance: float = 0.0
    closest_winzone_distance: float | None = None
    record_key: str = ""
    storage_path: str = ""
    settings_identifier: str | None = None
    settings_transitions: list[tuple[int, str]] = dataclasses.field(default_factory=list)
    release_offset_us: int | None = None
    events: list[tuple[int, int]] = dataclasses.field(default_factory=list)
    seen_events: set[tuple[int, int]] = dataclasses.field(default_factory=set)
    event_states: dict[int, ReplayEventState] = dataclasses.field(default_factory=dict)
    braking: bool = False
    outcome: str = "death"
    death_reason: str = ""
    finish_seconds: float | None = None
    finish_turns: int | None = None
    personal_best: bool = False

    def update_identity(self, player: Player) -> None:
        self.identity_key = player.identity_key
        self.username = player.record_name
        self.authenticated = bool(player.auth_name)

    def update_state(
        self,
        game_time: float,
        x: float,
        y: float,
        xdir: float,
        ydir: float,
        speed: float,
        turns: int,
        distance: float | None = None,
        released: bool = False,
    ) -> None:
        if not all(math.isfinite(value) for value in (game_time, x, y, xdir, ydir, speed)):
            return
        if distance is not None and math.isfinite(distance):
            self.latest_distance = max(self.initial_distance, float(distance))
        if released:
            # The replay begins at the authoritative start-hold release.  Later
            # state messages describe the live/terminal cycle and must not
            # overwrite the start used by ghost playback.
            self.x = x
            self.y = y
            self.xdir = xdir
            self.ydir = ydir
            self.speed = max(0.0, speed)
            self.initial_turns = max(0, turns)
            self.release_offset_us = round(
                (game_time - self.spawn_game_time) * 1_000_000
            )

    def add_input(
        self,
        game_time: float,
        action_name: str,
        state: ReplayEventState | None = None,
    ) -> bool:
        action = REPLAY_ACTION_CODES.get(action_name)
        if action is None or not math.isfinite(game_time):
            return False
        if action_name.startswith("B"):
            braking = action_name == "B1"
            if braking == self.braking:
                return False
            self.braking = braking
        offset_us = round((game_time - self.spawn_game_time) * 1_000_000)
        event = (offset_us, action)
        if event in self.seen_events:
            return False
        self.seen_events.add(event)
        event_index = len(self.events)
        self.events.append(event)
        if state is not None:
            self.event_states[event_index] = state
        return True

    def add_settings_transition(self, game_time: float, identifier: str) -> bool:
        if not identifier or not math.isfinite(game_time):
            return False
        current = (
            self.settings_transitions[-1][1]
            if self.settings_transitions
            else self.settings_identifier
        )
        if identifier == current:
            return False
        offset_us = round((game_time - self.spawn_game_time) * 1_000_000)
        if offset_us <= 0 and not self.settings_transitions:
            self.settings_identifier = identifier
            return True
        self.settings_transitions.append((max(0, offset_us), identifier))
        return True


@dataclasses.dataclass
class ReplaySettingsAssembly:
    format_version: int
    expected_count: int
    items: list[tuple[bytes, bytes]] = dataclasses.field(default_factory=list)


@dataclasses.dataclass(frozen=True)
class Record:
    identity_key: str
    username: str
    best_seconds: float
    authenticated: bool
    best_turns: int | None = None
    achieved_at: float | None = None


@dataclasses.dataclass(frozen=True)
class GhostReplay:
    run_id: int
    identity_key: str
    username: str
    resource_key: str
    map_identifier: str
    revision_identifier: str
    finish_seconds: float
    finish_turns: int | None
    x: float
    y: float
    xdir: float
    ydir: float
    speed: float
    initial_turns: int
    size_factor: float | None
    events: tuple[tuple[int, int], ...]
    event_states: tuple[ReplayEventState | None, ...] = ()
    settings_identifier: str | None = None
    settings_identifiers: tuple[str, ...] = ()
    finished: bool = True
    closest_winzone_distance: float | None = None


@dataclasses.dataclass(frozen=True)
class StoredIdentity:
    identity_key: str
    username: str
    authenticated: bool


@dataclasses.dataclass(frozen=True)
class UserMergeResult:
    records_moved: int
    finishes_moved: int
    overlapping_records: int
    replay_runs_moved: int = 0


@dataclasses.dataclass(frozen=True)
class ReplayMapKeyMigration:
    map_rows: int = 0
    replay_runs: int = 0
    finished_runs: int = 0
    records_marked: int = 0
    earliest_finished_run_id: int | None = None
    previous_cursor: int = 0
    replay_cursor: int = 0


@dataclasses.dataclass(frozen=True)
class SavedPlayerMessage:
    id: int
    recipient_identity_key: str
    recipient_name: str
    sender_identity_key: str
    sender_name: str
    message: str
    created_at: float


class StateStore:
    FINISH_HISTORY_BACKFILL_KEY = "schema:finish-history-backfill-v1"
    PLAYER_STATS_BACKFILL_KEY = "schema:player-stats-backfill-v1"

    def __init__(self, path: Path):
        path.parent.mkdir(parents=True, exist_ok=True)
        self.path = path
        self.owner_thread_id = threading.get_ident()
        self.thread_connections = threading.local()
        self.connection = sqlite3.connect(path)
        self.connection.execute("PRAGMA journal_mode=WAL")
        self.connection.execute("PRAGMA synchronous=FULL")
        self.connection.executescript(
            """
            CREATE TABLE IF NOT EXISTS records (
                map_key TEXT NOT NULL,
                identity_key TEXT NOT NULL,
                username TEXT NOT NULL,
                authenticated INTEGER NOT NULL,
                best_seconds REAL NOT NULL,
                best_turns INTEGER,
                achieved_at REAL NOT NULL,
                replay_available INTEGER NOT NULL DEFAULT 0,
                PRIMARY KEY (map_key, identity_key)
            );
            CREATE INDEX IF NOT EXISTS records_by_map_time
                ON records(map_key, best_seconds, achieved_at);
            CREATE TABLE IF NOT EXISTS finishes (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                map_key TEXT NOT NULL,
                identity_key TEXT NOT NULL,
                username TEXT NOT NULL,
                authenticated INTEGER NOT NULL,
                seconds REAL NOT NULL,
                turns INTEGER,
                finished_at REAL NOT NULL
            );
            CREATE INDEX IF NOT EXISTS finishes_by_map_identity_time
                ON finishes(map_key, identity_key, seconds);
            CREATE TABLE IF NOT EXISTS ratings (
                map_key TEXT NOT NULL,
                identity_key TEXT NOT NULL,
                username TEXT NOT NULL,
                authenticated INTEGER NOT NULL,
                rating INTEGER NOT NULL CHECK(rating BETWEEN 1 AND 5),
                previous_rating INTEGER CHECK(
                    previous_rating IS NULL OR previous_rating BETWEEN 1 AND 5
                ),
                undo_available INTEGER NOT NULL DEFAULT 1,
                rated_at REAL NOT NULL,
                PRIMARY KEY (map_key, identity_key)
            );
            CREATE INDEX IF NOT EXISTS ratings_by_map
                ON ratings(map_key);
            CREATE TABLE IF NOT EXISTS metadata (
                key TEXT PRIMARY KEY,
                value TEXT NOT NULL
            );
            CREATE TABLE IF NOT EXISTS player_messages (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                recipient_identity_key TEXT NOT NULL,
                recipient_name TEXT NOT NULL,
                sender_identity_key TEXT NOT NULL,
                sender_name TEXT NOT NULL,
                message TEXT NOT NULL,
                created_at REAL NOT NULL
            );
            CREATE INDEX IF NOT EXISTS player_messages_by_recipient
                ON player_messages(recipient_identity_key, id);
            CREATE TABLE IF NOT EXISTS replay_maps (
                id INTEGER PRIMARY KEY,
                map_identifier TEXT NOT NULL,
                revision_identifier TEXT NOT NULL,
                resource_key TEXT NOT NULL,
                record_key TEXT NOT NULL DEFAULT '',
                storage_path TEXT NOT NULL DEFAULT '',
                UNIQUE(map_identifier, revision_identifier, resource_key)
            );
            CREATE TABLE IF NOT EXISTS replay_players (
                id INTEGER PRIMARY KEY,
                identity_key TEXT NOT NULL UNIQUE,
                username TEXT NOT NULL,
                authenticated INTEGER NOT NULL
            );
            CREATE TABLE IF NOT EXISTS replay_settings (
                id INTEGER PRIMARY KEY,
                server_identifier TEXT NOT NULL UNIQUE,
                fingerprint_sha256 TEXT NOT NULL UNIQUE,
                format_version INTEGER NOT NULL,
                setting_count INTEGER NOT NULL,
                compression INTEGER NOT NULL,
                setting_data BLOB NOT NULL
            );
            CREATE TABLE IF NOT EXISTS replay_runs (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                map_ref INTEGER NOT NULL REFERENCES replay_maps(id),
                player_ref INTEGER NOT NULL REFERENCES replay_players(id),
                recorded_at REAL NOT NULL,
                ended_at REAL NOT NULL,
                spawn_game_time REAL NOT NULL,
                release_offset_us INTEGER,
                start_x REAL NOT NULL,
                start_y REAL NOT NULL,
                start_xdir REAL NOT NULL,
                start_ydir REAL NOT NULL,
                start_speed REAL NOT NULL,
                initial_turns INTEGER NOT NULL,
                size_factor REAL,
                start_mode INTEGER NOT NULL,
                checkpoint_spawn INTEGER NOT NULL,
                settings_ref INTEGER REFERENCES replay_settings(id),
                outcome INTEGER NOT NULL,
                death_reason TEXT NOT NULL,
                finish_seconds REAL,
                finish_turns INTEGER,
                personal_best INTEGER NOT NULL,
                event_count INTEGER NOT NULL,
                format_version INTEGER NOT NULL,
                input_data BLOB NOT NULL,
                closest_winzone_distance REAL
            );
            CREATE INDEX IF NOT EXISTS replay_runs_by_player
                ON replay_runs(player_ref, recorded_at DESC);
            CREATE INDEX IF NOT EXISTS replay_runs_by_map
                ON replay_runs(map_ref, recorded_at DESC);
            CREATE INDEX IF NOT EXISTS replay_runs_personal_bests
                ON replay_runs(player_ref, map_ref, personal_best)
                WHERE personal_best = 1;
            CREATE TABLE IF NOT EXISTS player_stats (
                identity_key TEXT PRIMARY KEY,
                username TEXT NOT NULL,
                authenticated INTEGER NOT NULL,
                play_seconds REAL NOT NULL DEFAULT 0,
                rubber_deaths INTEGER NOT NULL DEFAULT 0,
                deathzone_deaths INTEGER NOT NULL DEFAULT 0,
                finishes INTEGER NOT NULL DEFAULT 0,
                distance_meters REAL NOT NULL DEFAULT 0,
                turns INTEGER NOT NULL DEFAULT 0,
                updated_at REAL NOT NULL
            );
            CREATE TABLE IF NOT EXISTS replay_setting_transitions (
                run_ref INTEGER NOT NULL REFERENCES replay_runs(id) ON DELETE CASCADE,
                offset_us INTEGER NOT NULL,
                settings_ref INTEGER NOT NULL REFERENCES replay_settings(id),
                PRIMARY KEY(run_ref, offset_us, settings_ref)
            );
            CREATE TABLE IF NOT EXISTS replay_event_states (
                run_ref INTEGER NOT NULL REFERENCES replay_runs(id) ON DELETE CASCADE,
                event_index INTEGER NOT NULL,
                x REAL NOT NULL,
                y REAL NOT NULL,
                xdir REAL NOT NULL,
                ydir REAL NOT NULL,
                speed REAL NOT NULL,
                turns INTEGER NOT NULL,
                PRIMARY KEY(run_ref, event_index)
            );
            """
        )
        record_columns = {
            row[1] for row in self.connection.execute("PRAGMA table_info(records)")
        }
        if "best_turns" not in record_columns:
            self.connection.execute("ALTER TABLE records ADD COLUMN best_turns INTEGER")
        if "replay_available" not in record_columns:
            self.connection.execute(
                "ALTER TABLE records ADD COLUMN replay_available INTEGER NOT NULL DEFAULT 0"
            )
        finish_columns = {
            row[1] for row in self.connection.execute("PRAGMA table_info(finishes)")
        }
        if "turns" not in finish_columns:
            self.connection.execute("ALTER TABLE finishes ADD COLUMN turns INTEGER")
        backfill_complete = self.connection.execute(
            "SELECT 1 FROM metadata WHERE key=?",
            (self.FINISH_HISTORY_BACKFILL_KEY,),
        ).fetchone()
        if backfill_complete is None:
            # Older databases may contain personal-best rows from before complete
            # finish history was introduced. This migration used to scan the full
            # finish table at every server-script start; the indexed, durable
            # marker keeps it off the reload path after the one required pass.
            self.connection.execute(
                "INSERT INTO finishes(map_key, identity_key, username, authenticated, "
                "seconds, turns, finished_at) "
                "SELECT records.map_key, records.identity_key, records.username, "
                "records.authenticated, records.best_seconds, records.best_turns, "
                "records.achieved_at FROM records WHERE NOT EXISTS ("
                "SELECT 1 FROM finishes WHERE finishes.map_key=records.map_key "
                "AND finishes.identity_key=records.identity_key "
                "AND finishes.seconds=records.best_seconds "
                "AND (finishes.turns=records.best_turns OR "
                "(finishes.turns IS NULL AND records.best_turns IS NULL)))"
            )
            self.connection.execute(
                "INSERT INTO metadata(key, value) VALUES(?, 'true')",
                (self.FINISH_HISTORY_BACKFILL_KEY,),
            )
        replay_run_columns = {
            row[1] for row in self.connection.execute("PRAGMA table_info(replay_runs)")
        }
        if "settings_ref" not in replay_run_columns:
            self.connection.execute(
                "ALTER TABLE replay_runs ADD COLUMN settings_ref INTEGER "
                "REFERENCES replay_settings(id)"
            )
        if "distance_meters" not in replay_run_columns:
            self.connection.execute(
                "ALTER TABLE replay_runs ADD COLUMN distance_meters REAL "
                "NOT NULL DEFAULT 0"
            )
        if "turns_driven" not in replay_run_columns:
            self.connection.execute(
                "ALTER TABLE replay_runs ADD COLUMN turns_driven INTEGER "
                "NOT NULL DEFAULT 0"
            )
        if "closest_winzone_distance" not in replay_run_columns:
            self.connection.execute(
                "ALTER TABLE replay_runs ADD COLUMN closest_winzone_distance REAL"
            )
        self.connection.execute(
            "CREATE INDEX IF NOT EXISTS replay_runs_unfinished_progress "
            "ON replay_runs(player_ref, map_ref, closest_winzone_distance) "
            "WHERE outcome IN (0, 3) AND checkpoint_spawn=0 "
            "AND closest_winzone_distance IS NOT NULL"
        )
        replay_map_columns = {
            row[1] for row in self.connection.execute("PRAGMA table_info(replay_maps)")
        }
        if "record_key" not in replay_map_columns:
            self.connection.execute(
                "ALTER TABLE replay_maps ADD COLUMN record_key TEXT NOT NULL DEFAULT ''"
            )
        if "storage_path" not in replay_map_columns:
            self.connection.execute(
                "ALTER TABLE replay_maps ADD COLUMN storage_path TEXT NOT NULL DEFAULT ''"
            )
        self.connection.execute(
            "UPDATE replay_maps SET record_key=resource_key WHERE record_key=''"
        )
        self._backfill_player_stats()
        self.connection.commit()

    @staticmethod
    def _replay_death_counts(reason: str) -> tuple[int, int]:
        """Classify public racing deaths without counting administrative kills."""
        parts = str(reason or "").strip().split(maxsplit=1)
        kind = parts[0].upper() if parts else ""
        if kind in {"DEATHZONE", "DEATHZONE_TEAM"}:
            return 0, 1
        if kind in {
            "FRAG",
            "OTHER",
            "RUBBERZONE",
            "SUICIDE",
            "TEAMKILL",
            "UNKNOWN",
        }:
            return 1, 0
        return 0, 0

    @staticmethod
    def _replay_turn_count(input_data: bytes) -> int:
        return sum(
            1 for _offset, action in decode_replay_inputs(bytes(input_data))
            if action in {REPLAY_ACTION_CODES["L"], REPLAY_ACTION_CODES["R"]}
        )

    def _backfill_player_stats(self) -> None:
        marker = self.connection.execute(
            "SELECT 1 FROM metadata WHERE key=?",
            (self.PLAYER_STATS_BACKFILL_KEY,),
        ).fetchone()
        if marker is not None:
            return

        # Rebuild instead of incrementing so an interrupted migration is safe
        # to run again. Replays provide time, death cause, distance and turns;
        # the finishes table remains the authority for completed attempts.
        self.connection.execute("DELETE FROM player_stats")
        identities: dict[str, list[object]] = {}
        for identity_key, username, authenticated, saved_at in self.connection.execute(
            "SELECT identity_key, username, authenticated, achieved_at AS saved_at FROM records "
            "UNION ALL SELECT identity_key, username, authenticated, finished_at "
            "FROM finishes UNION ALL SELECT replay_players.identity_key, "
            "replay_players.username, replay_players.authenticated, "
            "MAX(replay_runs.recorded_at) FROM replay_players JOIN replay_runs "
            "ON replay_runs.player_ref=replay_players.id GROUP BY replay_players.id "
            "ORDER BY saved_at ASC"
        ):
            identities[str(identity_key)] = [
                str(username), bool(authenticated), 0.0, 0, 0, 0, 0.0, 0,
                float(saved_at or 0),
            ]
        for identity_key, finish_count, finished_at in self.connection.execute(
            "SELECT identity_key, COUNT(*), MAX(finished_at) FROM finishes "
            "GROUP BY identity_key"
        ):
            if str(identity_key) in identities:
                identities[str(identity_key)][5] = int(finish_count)
                identities[str(identity_key)][8] = max(
                    float(identities[str(identity_key)][8]), float(finished_at or 0)
                )
        for row in self.connection.execute(
            "SELECT replay_players.identity_key, replay_runs.recorded_at, "
            "replay_runs.ended_at, replay_runs.outcome, replay_runs.death_reason, "
            "replay_runs.distance_meters, replay_runs.turns_driven, "
            "replay_runs.input_data FROM replay_runs JOIN replay_players "
            "ON replay_players.id=replay_runs.player_ref"
        ):
            identity_key = str(row[0])
            values = identities.get(identity_key)
            if values is None:
                continue
            values[2] = float(values[2]) + max(0.0, float(row[2]) - float(row[1]))
            if int(row[3]) == 0:
                rubber, deathzone = self._replay_death_counts(str(row[4]))
                values[3] = int(values[3]) + rubber
                values[4] = int(values[4]) + deathzone
            values[6] = float(values[6]) + max(0.0, float(row[5] or 0))
            stored_turns = max(0, int(row[6] or 0))
            if stored_turns == 0 and row[7]:
                stored_turns = self._replay_turn_count(row[7])
            values[7] = int(values[7]) + stored_turns
            values[8] = max(float(values[8]), float(row[2] or 0))

        self.connection.executemany(
            "INSERT INTO player_stats(identity_key, username, authenticated, "
            "play_seconds, rubber_deaths, deathzone_deaths, finishes, "
            "distance_meters, turns, updated_at) VALUES(?, ?, ?, ?, ?, ?, ?, ?, ?, ?)",
            [
                (identity_key, values[0], int(values[1]), *values[2:])
                for identity_key, values in identities.items()
            ],
        )
        self.connection.execute(
            "INSERT INTO metadata(key, value) VALUES(?, 'true')",
            (self.PLAYER_STATS_BACKFILL_KEY,),
        )

    def _increment_player_stats(
        self,
        identity_key: str,
        username: str,
        authenticated: bool,
        *,
        play_seconds: float = 0,
        rubber_deaths: int = 0,
        deathzone_deaths: int = 0,
        finishes: int = 0,
        distance_meters: float = 0,
        turns: int = 0,
        updated_at: float | None = None,
    ) -> None:
        self.connection.execute(
            "INSERT INTO player_stats(identity_key, username, authenticated, "
            "play_seconds, rubber_deaths, deathzone_deaths, finishes, "
            "distance_meters, turns, updated_at) VALUES(?, ?, ?, ?, ?, ?, ?, ?, ?, ?) "
            "ON CONFLICT(identity_key) DO UPDATE SET username=excluded.username, "
            "authenticated=excluded.authenticated, "
            "play_seconds=player_stats.play_seconds+excluded.play_seconds, "
            "rubber_deaths=player_stats.rubber_deaths+excluded.rubber_deaths, "
            "deathzone_deaths=player_stats.deathzone_deaths+excluded.deathzone_deaths, "
            "finishes=player_stats.finishes+excluded.finishes, "
            "distance_meters=player_stats.distance_meters+excluded.distance_meters, "
            "turns=player_stats.turns+excluded.turns, "
            "updated_at=MAX(player_stats.updated_at, excluded.updated_at)",
            (
                identity_key,
                username,
                int(authenticated),
                max(0.0, float(play_seconds)),
                max(0, int(rubber_deaths)),
                max(0, int(deathzone_deaths)),
                max(0, int(finishes)),
                max(0.0, float(distance_meters)),
                max(0, int(turns)),
                float(updated_at if updated_at is not None else time.time()),
            ),
        )

    def current_connection(self) -> sqlite3.Connection:
        """Use one WAL connection per worker without sharing SQLite objects."""
        if threading.get_ident() == self.owner_thread_id:
            return self.connection
        connection = getattr(self.thread_connections, "connection", None)
        if connection is None:
            connection = sqlite3.connect(self.path, timeout=30.0)
            connection.execute("PRAGMA journal_mode=WAL")
            connection.execute("PRAGMA busy_timeout=30000")
            self.thread_connections.connection = connection
        return connection

    def close(self) -> None:
        self.connection.close()

    def get_json(self, key: str, default):
        row = self.current_connection().execute(
            "SELECT value FROM metadata WHERE key = ?", (key,)
        ).fetchone()
        if not row:
            return default
        try:
            return json.loads(row[0])
        except json.JSONDecodeError:
            return default

    def set_json(self, key: str, value) -> None:
        encoded = json.dumps(value, separators=(",", ":"), ensure_ascii=False)
        connection = self.current_connection()
        connection.execute(
            "INSERT INTO metadata(key, value) VALUES(?, ?) "
            "ON CONFLICT(key) DO UPDATE SET value=excluded.value",
            (key, encoded),
        )
        connection.commit()

    def rekey_replay_maps(
        self,
        record_keys_by_resource: dict[str, str],
        server_id: str,
    ) -> ReplayMapKeyMigration:
        """Attach stable leaderboard keys without discarding exact map resources."""
        aliases = {
            str(resource_key).strip(): str(record_key).strip()
            for resource_key, record_key in record_keys_by_resource.items()
            if str(resource_key).strip()
            and str(record_key).strip()
            and str(resource_key).strip() != str(record_key).strip()
        }
        cursor_key = f"live_dashboard_replay_cursor_{server_id}"
        connection = self.current_connection()
        cursor_row = connection.execute(
            "SELECT value FROM metadata WHERE key=?", (cursor_key,)
        ).fetchone()
        try:
            previous_cursor = (
                max(0, int(json.loads(cursor_row[0]))) if cursor_row else 0
            )
        except (TypeError, ValueError, json.JSONDecodeError):
            previous_cursor = 0
        if not aliases:
            return ReplayMapKeyMigration(
                previous_cursor=previous_cursor,
                replay_cursor=previous_cursor,
            )

        map_rows = 0
        replay_runs = 0
        finished_runs = 0
        records_marked = 0
        earliest_finished_run_id: int | None = None
        target_keys: set[str] = set()
        connection.execute("BEGIN IMMEDIATE")
        try:
            for resource_key, record_key in sorted(aliases.items()):
                rows = connection.execute(
                    "SELECT id FROM replay_maps WHERE record_key=? ORDER BY id",
                    (resource_key,),
                ).fetchall()
                for (map_ref,) in rows:
                    run_summary = connection.execute(
                        "SELECT COUNT(*), SUM(CASE WHEN outcome=1 AND "
                        "finish_seconds IS NOT NULL THEN 1 ELSE 0 END), "
                        "MIN(CASE WHEN outcome=1 AND finish_seconds IS NOT NULL "
                        "THEN id END) FROM replay_runs WHERE map_ref=?",
                        (map_ref,),
                    ).fetchone()
                    replay_runs += int(run_summary[0] or 0)
                    finished_runs += int(run_summary[1] or 0)
                    if run_summary[2] is not None:
                        run_id = int(run_summary[2])
                        earliest_finished_run_id = (
                            run_id
                            if earliest_finished_run_id is None
                            else min(earliest_finished_run_id, run_id)
                        )
                    connection.execute(
                        "UPDATE replay_maps SET record_key=? WHERE id=?",
                        (record_key, map_ref),
                    )
                    map_rows += 1
                    target_keys.add(record_key)

            for record_key in sorted(target_keys):
                marked = connection.execute(
                    "UPDATE records SET replay_available=1 WHERE map_key=? AND "
                    "authenticated=1 AND replay_available=0 AND EXISTS ("
                    "SELECT 1 FROM replay_runs JOIN replay_maps ON "
                    "replay_maps.id=replay_runs.map_ref JOIN replay_players ON "
                    "replay_players.id=replay_runs.player_ref WHERE "
                    "replay_maps.record_key=records.map_key AND "
                    "replay_players.identity_key=records.identity_key AND "
                    "replay_runs.outcome=1 AND "
                    "replay_runs.finish_seconds IS NOT NULL)",
                    (record_key,),
                )
                records_marked += int(marked.rowcount)

            replay_cursor = previous_cursor
            if earliest_finished_run_id is not None:
                replay_cursor = min(
                    previous_cursor, max(0, earliest_finished_run_id - 1)
                )
                if replay_cursor != previous_cursor:
                    connection.execute(
                        "INSERT INTO metadata(key, value) VALUES(?, ?) "
                        "ON CONFLICT(key) DO UPDATE SET value=excluded.value",
                        (
                            cursor_key,
                            json.dumps(replay_cursor, separators=(",", ":")),
                        ),
                    )
            connection.commit()
        except Exception:
            connection.rollback()
            raise
        return ReplayMapKeyMigration(
            map_rows=map_rows,
            replay_runs=replay_runs,
            finished_runs=finished_runs,
            records_marked=records_marked,
            earliest_finished_run_id=earliest_finished_run_id,
            previous_cursor=previous_cursor,
            replay_cursor=replay_cursor,
        )

    def save_player_message(
        self,
        recipient: StoredIdentity,
        sender: StoredIdentity,
        message: str,
        *,
        created_at: float | None = None,
    ) -> SavedPlayerMessage:
        if (
            not recipient.authenticated
            or not recipient.identity_key.startswith("auth:")
        ):
            raise ValueError("saved messages require an authenticated recipient")
        text = plain_console_text(message).strip()
        if not text:
            raise ValueError("saved message is empty")
        if len(text) > PLAYER_MESSAGE_LIMIT:
            raise ValueError(
                f"saved messages may be at most {PLAYER_MESSAGE_LIMIT} characters"
            )
        connection = self.current_connection()
        recipient_count = int(connection.execute(
            "SELECT COUNT(*) FROM player_messages WHERE recipient_identity_key=?",
            (recipient.identity_key,),
        ).fetchone()[0])
        if recipient_count >= PLAYER_MESSAGE_PENDING_LIMIT:
            raise OverflowError("that player already has the maximum pending messages")
        global_count = int(connection.execute(
            "SELECT COUNT(*) FROM player_messages"
        ).fetchone()[0])
        if global_count >= PLAYER_MESSAGE_GLOBAL_LIMIT:
            raise OverflowError("the server message queue is full")
        timestamp = time.time() if created_at is None else float(created_at)
        cursor = connection.execute(
            "INSERT INTO player_messages("
            "recipient_identity_key, recipient_name, sender_identity_key, "
            "sender_name, message, created_at) VALUES(?, ?, ?, ?, ?, ?)",
            (
                recipient.identity_key,
                recipient.username,
                sender.identity_key,
                sender.username,
                text,
                timestamp,
            ),
        )
        connection.commit()
        return SavedPlayerMessage(
            int(cursor.lastrowid),
            recipient.identity_key,
            recipient.username,
            sender.identity_key,
            sender.username,
            text,
            timestamp,
        )

    def pending_player_messages(
        self,
        identity_key: str,
        limit: int = PLAYER_MESSAGE_PENDING_LIMIT,
    ) -> list[SavedPlayerMessage]:
        rows = self.current_connection().execute(
            "SELECT id, recipient_identity_key, recipient_name, "
            "sender_identity_key, sender_name, message, created_at "
            "FROM player_messages WHERE recipient_identity_key=? "
            "ORDER BY id LIMIT ?",
            (
                identity_key,
                max(1, min(int(limit), PLAYER_MESSAGE_PENDING_LIMIT)),
            ),
        ).fetchall()
        return [SavedPlayerMessage(*row) for row in rows]

    def delete_player_message(self, message_id: int, identity_key: str) -> bool:
        connection = self.current_connection()
        cursor = connection.execute(
            "DELETE FROM player_messages WHERE id=? AND recipient_identity_key=?",
            (int(message_id), identity_key),
        )
        connection.commit()
        return cursor.rowcount == 1

    def add_replay_settings(
        self,
        server_identifier: str,
        format_version: int,
        items: Iterable[tuple[bytes, bytes]],
    ) -> int:
        """Store one deduplicated settings state with a collision check."""
        values = list(items)
        uncompressed = encode_replay_settings(values)
        fingerprint = hashlib.sha256(uncompressed).hexdigest()
        existing = self.connection.execute(
            "SELECT id, fingerprint_sha256 FROM replay_settings "
            "WHERE server_identifier=?",
            (server_identifier,),
        ).fetchone()
        if existing:
            if existing[1] != fingerprint:
                raise ValueError(
                    f"replay settings identifier collision: {server_identifier}"
                )
            return int(existing[0])
        blob = zlib.compress(uncompressed, level=9)
        cursor = self.connection.execute(
            "INSERT INTO replay_settings(server_identifier, fingerprint_sha256, "
            "format_version, setting_count, compression, setting_data) "
            "VALUES(?, ?, ?, ?, ?, ?)",
            (
                server_identifier,
                fingerprint,
                format_version,
                len(values),
                1,
                sqlite3.Binary(blob),
            ),
        )
        self.connection.commit()
        return int(cursor.lastrowid)

    def replay_settings_ref(self, server_identifier: str | None) -> int | None:
        if not server_identifier:
            return None
        row = self.connection.execute(
            "SELECT id FROM replay_settings WHERE server_identifier=?",
            (server_identifier,),
        ).fetchone()
        return int(row[0]) if row else None

    def ghost_settings_compatible(
        self,
        recorded_identifier: str,
        active_identifier: str,
        *,
        ignore_size_factor: bool = False,
    ) -> bool:
        """Compare replay settings while excluding tolerated ghost differences."""
        if recorded_identifier == active_identifier:
            return True
        ignored_settings = (
            GHOST_NON_PHYSICS_REPLAY_SETTINGS
            | GHOST_TOLERATED_PHYSICS_REPLAY_SETTINGS
        )
        if ignore_size_factor:
            ignored_settings = ignored_settings | {b"SIZE_FACTOR"}
        rows = self.current_connection().execute(
            "SELECT server_identifier, format_version, compression, setting_data "
            "FROM replay_settings WHERE server_identifier IN (?, ?)",
            (recorded_identifier, active_identifier),
        ).fetchall()
        snapshots: dict[str, tuple[int, tuple[tuple[bytes, bytes], ...]]] = {}
        try:
            for identifier, format_version, compression, setting_data in rows:
                if int(compression) not in {0, 1}:
                    return False
                raw = (
                    zlib.decompress(bytes(setting_data))
                    if int(compression) == 1
                    else bytes(setting_data)
                )
                relevant_items = tuple(
                    sorted(
                        (name, value)
                        for name, value in decode_replay_settings(raw)
                        if name not in ignored_settings
                    )
                )
                snapshots[str(identifier)] = (int(format_version), relevant_items)
        except (TypeError, ValueError, zlib.error):
            return False
        return (
            len(snapshots) == 2
            and snapshots.get(recorded_identifier)
            == snapshots.get(active_identifier)
        )

    def ghost_start_speed(self, settings_identifier: str | None) -> float | None:
        """Recover a legacy replay's positive release speed from its settings."""
        if not settings_identifier:
            return None
        row = self.current_connection().execute(
            "SELECT compression, setting_data FROM replay_settings "
            "WHERE server_identifier=?",
            (settings_identifier,),
        ).fetchone()
        if row is None:
            return None
        try:
            if int(row[0]) not in {0, 1}:
                return None
            raw = zlib.decompress(bytes(row[1])) if int(row[0]) == 1 else bytes(row[1])
            settings = dict(decode_replay_settings(raw))
            speed = float(
                settings.get(
                    b"CYCLE_START_SPEED",
                    settings.get(b"CYCLE_SPEED", b""),
                )
            )
            factor = float(settings.get(b"REAL_CYCLE_SPEED_FACTOR", b"1"))
            result = speed * factor
        except (TypeError, ValueError, zlib.error):
            return None
        return result if math.isfinite(result) and result > 1e-12 else None

    def add_replay(self, capture: ReplayCapture, ended_at: float) -> int:
        """Persist one compact, physics-free cycle input stream."""
        record_key = capture.record_key or capture.resource_key
        self.connection.execute(
            "INSERT INTO replay_maps(map_identifier, revision_identifier, resource_key, "
            "record_key, storage_path) VALUES(?, ?, ?, ?, ?) "
            "ON CONFLICT(map_identifier, revision_identifier, resource_key) DO UPDATE SET "
            "record_key=excluded.record_key, storage_path=CASE WHEN excluded.storage_path!='' "
            "THEN excluded.storage_path ELSE replay_maps.storage_path END",
            (
                capture.map_identifier,
                capture.revision_identifier,
                capture.resource_key,
                record_key,
                capture.storage_path,
            ),
        )
        map_ref = self.connection.execute(
            "SELECT id FROM replay_maps WHERE map_identifier=? "
            "AND revision_identifier=? AND resource_key=?",
            (
                capture.map_identifier,
                capture.revision_identifier,
                capture.resource_key,
            ),
        ).fetchone()[0]
        self.connection.execute(
            "INSERT INTO replay_players(identity_key, username, authenticated) "
            "VALUES(?, ?, ?) ON CONFLICT(identity_key) DO UPDATE SET "
            "username=excluded.username, authenticated=excluded.authenticated",
            (
                capture.identity_key,
                capture.username,
                int(capture.authenticated),
            ),
        )
        player_ref = self.connection.execute(
            "SELECT id FROM replay_players WHERE identity_key=?",
            (capture.identity_key,),
        ).fetchone()[0]
        start_modes = {
            "brake": 0,
            "immediate": 1,
            "countdown": 2,
            "respawn": 3,
        }
        outcomes = {
            "death": 0,
            "finish": 1,
            "replaced": 2,
            "round_end": 3,
            "controller_stop": 4,
            "invalid_finish": 5,
        }
        blob = encode_replay_inputs(capture.events)
        distance_meters = max(
            0.0, float(capture.latest_distance) - float(capture.initial_distance)
        )
        turns_driven = sum(
            1 for _offset, action in capture.events
            if action in {REPLAY_ACTION_CODES["L"], REPLAY_ACTION_CODES["R"]}
        )
        settings_ref = self.replay_settings_ref(capture.settings_identifier)
        cursor = self.connection.execute(
            "INSERT INTO replay_runs("
            "map_ref, player_ref, recorded_at, ended_at, spawn_game_time, "
            "release_offset_us, start_x, start_y, start_xdir, start_ydir, "
            "start_speed, initial_turns, size_factor, start_mode, checkpoint_spawn, settings_ref, "
            "outcome, death_reason, finish_seconds, finish_turns, personal_best, "
            "event_count, format_version, input_data, distance_meters, turns_driven, "
            "closest_winzone_distance"
            ") VALUES(?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)",
            (
                map_ref,
                player_ref,
                capture.started_at,
                ended_at,
                capture.spawn_game_time,
                capture.release_offset_us,
                capture.x,
                capture.y,
                capture.xdir,
                capture.ydir,
                capture.speed,
                capture.initial_turns,
                capture.size_factor,
                start_modes.get(capture.start_mode, 0),
                int(capture.checkpoint_spawn),
                settings_ref,
                outcomes.get(capture.outcome, 0),
                capture.death_reason,
                capture.finish_seconds,
                capture.finish_turns,
                int(capture.personal_best),
                len(capture.events),
                REPLAY_FORMAT_VERSION,
                sqlite3.Binary(blob),
                distance_meters,
                turns_driven,
                capture.closest_winzone_distance,
            ),
        )
        run_ref = int(cursor.lastrowid)
        for event_index, state in capture.event_states.items():
            if event_index < 0 or event_index >= len(capture.events):
                continue
            self.connection.execute(
                "INSERT OR IGNORE INTO replay_event_states("
                "run_ref, event_index, x, y, xdir, ydir, speed, turns) "
                "VALUES(?, ?, ?, ?, ?, ?, ?, ?)",
                (
                    run_ref,
                    event_index,
                    state.x,
                    state.y,
                    state.xdir,
                    state.ydir,
                    state.speed,
                    state.turns,
                ),
            )
        for offset_us, identifier in capture.settings_transitions:
            transition_ref = self.replay_settings_ref(identifier)
            if transition_ref is None:
                LOG.warning(
                    "replay %s references unknown settings %s",
                    capture.token,
                    identifier,
                )
                continue
            self.connection.execute(
                "INSERT OR IGNORE INTO replay_setting_transitions"
                "(run_ref, offset_us, settings_ref) VALUES(?, ?, ?)",
                (run_ref, offset_us, transition_ref),
            )
        rubber_deaths, deathzone_deaths = (
            self._replay_death_counts(capture.death_reason)
            if capture.outcome == "death"
            else (0, 0)
        )
        self._increment_player_stats(
            capture.identity_key,
            capture.username,
            capture.authenticated,
            play_seconds=max(0.0, float(ended_at) - float(capture.started_at)),
            rubber_deaths=rubber_deaths,
            deathzone_deaths=deathzone_deaths,
            distance_meters=distance_meters,
            turns=turns_driven,
            updated_at=ended_at,
        )
        self.connection.commit()
        return run_ref

    def add_finish(
        self, map_key: str, player: Player, seconds: float, turns: int | None = None
    ) -> tuple[Record, bool, float | None, int | None]:
        now = time.time()
        authenticated = bool(player.auth_name)
        self.connection.execute(
            "INSERT INTO finishes(map_key, identity_key, username, authenticated, seconds, turns, finished_at) "
            "VALUES(?, ?, ?, ?, ?, ?, ?)",
            (
                map_key,
                player.identity_key,
                player.record_name,
                int(authenticated),
                seconds,
                turns,
                now,
            ),
        )
        self._increment_player_stats(
            player.identity_key,
            player.record_name,
            authenticated,
            finishes=1,
            updated_at=now,
        )
        old = self.connection.execute(
            "SELECT best_seconds, best_turns, achieved_at FROM records WHERE map_key=? AND identity_key=?",
            (map_key, player.identity_key),
        ).fetchone()
        previous_best = float(old[0]) if old is not None else None
        previous_best_turns = (
            int(old[1]) if old is not None and old[1] is not None else None
        )
        previous_achieved_at = (
            float(old[2]) if old is not None and old[2] is not None else None
        )
        improved = (
            previous_best is None
            or seconds < previous_best
            or (
                seconds == previous_best
                and turns is not None
                and (previous_best_turns is None or turns < previous_best_turns)
            )
        )
        if improved:
            self.connection.execute(
                "INSERT INTO records(map_key, identity_key, username, authenticated, best_seconds, best_turns, achieved_at) "
                "VALUES(?, ?, ?, ?, ?, ?, ?) "
                "ON CONFLICT(map_key, identity_key) DO UPDATE SET "
                "username=excluded.username, authenticated=excluded.authenticated, "
                "best_seconds=excluded.best_seconds, best_turns=excluded.best_turns, "
                "achieved_at=excluded.achieved_at",
                (
                    map_key,
                    player.identity_key,
                    player.record_name,
                    int(authenticated),
                    seconds,
                    turns,
                    now,
                ),
            )
        else:
            self.connection.execute(
                "UPDATE records SET username=?, authenticated=? WHERE map_key=? AND identity_key=?",
                (player.record_name, int(authenticated), map_key, player.identity_key),
            )
        self.connection.commit()
        best = seconds if improved else float(previous_best)
        best_turns = turns if improved else previous_best_turns
        return (
            Record(
                player.identity_key,
                player.record_name,
                best,
                authenticated,
                best_turns,
                now if improved else previous_achieved_at,
            ),
            improved,
            previous_best,
            previous_best_turns,
        )

    def records(self, map_key: str) -> list[Record]:
        rows = self.connection.execute(
            "SELECT identity_key, username, best_seconds, authenticated, best_turns, achieved_at "
            "FROM records WHERE map_key=? ORDER BY best_seconds ASC, "
            "best_turns IS NULL ASC, best_turns ASC, achieved_at ASC",
            (map_key,),
        ).fetchall()
        return [
            Record(
                row[0],
                row[1],
                float(row[2]),
                bool(row[3]),
                int(row[4]) if row[4] is not None else None,
                float(row[5]) if row[5] is not None else None,
            )
            for row in rows
        ]

    def ghost_replays_for_record(
        self,
        record_key: str,
        record: Record,
        map_keys: Iterable[str] = (),
    ) -> tuple[GhostReplay, ...]:
        """Return ranked-first full-run replay candidates for one player."""
        return self._ghost_replays_for_player(
            record_key,
            record.identity_key,
            map_keys,
            ranked_record=record,
        )

    def ghost_replays_for_unfinished_pb(
        self,
        record_key: str,
        identity_key: str,
        map_keys: Iterable[str] = (),
    ) -> tuple[GhostReplay, ...]:
        """Return closest-to-winzone unfinished replay candidates."""
        return self._ghost_replays_for_player(
            record_key,
            identity_key,
            map_keys,
            ranked_record=None,
        )

    def _ghost_replays_for_player(
        self,
        record_key: str,
        identity_key: str,
        map_keys: Iterable[str],
        *,
        ranked_record: Record | None,
    ) -> tuple[GhostReplay, ...]:
        connection = self.current_connection()
        requested_map_keys = sorted(
            {
                str(value).strip()
                for value in (record_key, *map_keys)
                if str(value).strip()
            }
        )
        placeholders = ",".join("?" for _ in requested_map_keys)
        select = (
            "SELECT replay_runs.id, replay_players.identity_key, "
            "replay_players.username, {duration}, replay_runs.finish_turns, "
            "replay_runs.start_x, replay_runs.start_y, replay_runs.start_xdir, "
            "replay_runs.start_ydir, replay_runs.start_speed, "
            "replay_runs.initial_turns, replay_runs.size_factor, "
            "replay_runs.release_offset_us, replay_runs.input_data, "
            "replay_settings.server_identifier, replay_maps.resource_key, "
            "replay_maps.map_identifier, replay_maps.revision_identifier, "
            "replay_runs.closest_winzone_distance FROM replay_runs "
            "JOIN replay_players ON replay_players.id=replay_runs.player_ref "
            "JOIN replay_maps ON replay_maps.id=replay_runs.map_ref "
            "LEFT JOIN replay_settings ON replay_settings.id=replay_runs.settings_ref "
            f"WHERE (replay_maps.record_key IN ({placeholders}) OR "
            f"replay_maps.resource_key IN ({placeholders})) "
            "AND replay_players.identity_key=? "
            "AND replay_runs.checkpoint_spawn=0 "
            "AND replay_runs.format_version=? "
        )
        common_parameters = (
            *requested_map_keys,
            *requested_map_keys,
            identity_key,
            REPLAY_FORMAT_VERSION,
        )
        if ranked_record is not None:
            rows = connection.execute(
                select.format(duration="replay_runs.finish_seconds")
                + "AND replay_runs.outcome=1 "
                "ORDER BY CASE WHEN replay_runs.finish_seconds=? AND "
                "(replay_runs.finish_turns=? OR (replay_runs.finish_turns IS NULL "
                "AND ? IS NULL)) THEN 0 ELSE 1 END, "
                "replay_runs.finish_seconds ASC, replay_runs.finish_turns IS NULL, "
                "replay_runs.finish_turns ASC, replay_runs.recorded_at DESC, "
                "replay_runs.id DESC LIMIT ?",
                (
                    *common_parameters,
                    ranked_record.best_seconds,
                    ranked_record.best_turns,
                    ranked_record.best_turns,
                    GHOST_REPLAY_CANDIDATE_LIMIT,
                ),
            ).fetchall()
        else:
            duration = (
                "MAX(0.001, replay_runs.ended_at - replay_runs.recorded_at - "
                "COALESCE(replay_runs.release_offset_us, 0) / 1000000.0)"
            )
            rows = connection.execute(
                select.format(duration=duration)
                + "AND replay_runs.outcome IN (0, 3) "
                "AND replay_runs.closest_winzone_distance IS NOT NULL "
                "ORDER BY replay_runs.closest_winzone_distance ASC, "
                "replay_runs.recorded_at DESC, replay_runs.id DESC LIMIT ?",
                (*common_parameters, GHOST_REPLAY_CANDIDATE_LIMIT),
            ).fetchall()
        replays: list[GhostReplay] = []
        for row in rows:
            finish_seconds = float(row[3])
            if (
                not math.isfinite(finish_seconds)
                or finish_seconds <= 0
                or finish_seconds > GHOST_MAX_DURATION_SECONDS
            ):
                continue
            release_offset_us = int(row[12] or 0)
            try:
                decoded_events = decode_replay_inputs(bytes(row[13]))
            except (TypeError, ValueError):
                continue
            state_rows = connection.execute(
                "SELECT event_index, x, y, xdir, ydir, speed, turns "
                "FROM replay_event_states WHERE run_ref=? ORDER BY event_index",
                (int(row[0]),),
            ).fetchall()
            saved_states: dict[int, ReplayEventState] = {}
            for state_row in state_rows:
                try:
                    state = ReplayEventState(
                        *(float(value) for value in state_row[1:6]),
                        int(state_row[6]),
                    )
                except (TypeError, ValueError):
                    continue
                if (
                    all(
                        math.isfinite(value)
                        for value in (
                            state.x,
                            state.y,
                            state.xdir,
                            state.ydir,
                            state.speed,
                        )
                    )
                    and state.xdir * state.xdir + state.ydir * state.ydir > 1e-12
                    and state.speed > 1e-12
                    and 0 <= state.turns <= 65535
                ):
                    saved_states[int(state_row[0])] = state
            normalized_events_list: list[tuple[int, int]] = []
            normalized_states_list: list[ReplayEventState | None] = []
            for event_index, (offset_us, action) in enumerate(decoded_events):
                if int(offset_us) < release_offset_us:
                    continue
                normalized_events_list.append(
                    (int(offset_us) - release_offset_us, int(action))
                )
                normalized_states_list.append(saved_states.get(event_index))
            normalized_events = tuple(normalized_events_list)
            normalized_states = tuple(normalized_states_list)
            if len(normalized_events) > GHOST_MAX_EVENTS:
                continue
            duration_us = round(finish_seconds * 1_000_000)
            if any(
                offset_us < 0
                or offset_us > duration_us + 1_000_000
                or action not in range(len(REPLAY_ACTION_NAMES))
                for offset_us, action in normalized_events
            ):
                continue
            start_values = tuple(float(value) for value in row[5:11])
            if (
                not all(math.isfinite(value) for value in start_values)
                or start_values[2] ** 2 + start_values[3] ** 2 <= 1e-12
            ):
                continue
            settings_identifier = str(row[14]) if row[14] is not None else None
            transition_rows = connection.execute(
                "SELECT replay_settings.server_identifier FROM "
                "replay_setting_transitions JOIN replay_settings ON "
                "replay_settings.id=replay_setting_transitions.settings_ref "
                "WHERE replay_setting_transitions.run_ref=? ORDER BY "
                "replay_setting_transitions.offset_us",
                (int(row[0]),),
            ).fetchall()
            settings_identifiers = tuple(
                dict.fromkeys(
                    identifier
                    for identifier in (
                        settings_identifier,
                        *(str(item[0]) for item in transition_rows),
                    )
                    if identifier is not None
                )
            )
            replays.append(
                GhostReplay(
                    run_id=int(row[0]),
                    identity_key=str(row[1]),
                    username=str(row[2]),
                    resource_key=str(row[15]),
                    map_identifier=str(row[16]),
                    revision_identifier=str(row[17]),
                    finish_seconds=finish_seconds,
                    finish_turns=int(row[4]) if row[4] is not None else None,
                    x=start_values[0],
                    y=start_values[1],
                    xdir=start_values[2],
                    ydir=start_values[3],
                    speed=start_values[4],
                    initial_turns=max(0, min(65535, int(start_values[5]))),
                    size_factor=float(row[11]) if row[11] is not None else None,
                    events=normalized_events,
                    event_states=normalized_states,
                    settings_identifier=settings_identifier,
                    settings_identifiers=settings_identifiers,
                    finished=ranked_record is not None,
                    closest_winzone_distance=(
                        float(row[18]) if row[18] is not None else None
                    ),
                )
            )
        return tuple(replays)

    def map_ranks_for_player(
        self,
        map_keys: Iterable[str],
        identity_key: str,
    ) -> dict[str, int]:
        """Return the player's one-based rank for each map with a PB."""
        requested = sorted({str(map_key) for map_key in map_keys if map_key})
        ranks: dict[str, int] = {}
        connection = self.current_connection()
        for offset in range(0, len(requested), 500):
            batch = requested[offset : offset + 500]
            placeholders = ",".join("?" for _ in batch)
            rows = connection.execute(
                "SELECT map_key, player_rank FROM (SELECT map_key, identity_key, "
                "ROW_NUMBER() OVER (PARTITION BY map_key ORDER BY "
                "best_seconds ASC, best_turns IS NULL ASC, best_turns ASC, "
                "achieved_at ASC) AS player_rank FROM records WHERE map_key IN ("
                f"{placeholders})) WHERE identity_key = ?",
                [*batch, identity_key],
            ).fetchall()
            ranks.update(
                (str(map_key), int(player_rank))
                for map_key, player_rank in rows
            )
        return ranks

    def dashboard_record_rows(self) -> list[dict[str, object]]:
        """Return one local SQLite snapshot for precomputed public rankings."""
        connection = self.current_connection()
        rows = connection.execute(
            "SELECT map_key, identity_key, username, authenticated, best_seconds, "
            "best_turns, achieved_at, replay_available FROM records ORDER BY map_key, best_seconds, "
            "best_turns IS NULL ASC, best_turns ASC, achieved_at ASC"
        ).fetchall()
        replay_keys = {
            (str(row[0]), str(row[1]))
            for row in connection.execute(
                "SELECT DISTINCT replay_maps.record_key, "
                "replay_players.identity_key FROM replay_runs "
                "JOIN replay_players ON replay_players.id=replay_runs.player_ref "
                "JOIN replay_maps ON replay_maps.id=replay_runs.map_ref WHERE "
                "replay_runs.outcome=1 AND replay_runs.finish_seconds IS NOT NULL"
            ).fetchall()
        }
        return [
            {
                "mapKey": str(row[0]),
                "identityKey": str(row[1]),
                "username": str(row[2]),
                "authenticated": bool(row[3]),
                "bestSeconds": float(row[4]),
                "bestTurns": int(row[5]) if row[5] is not None else None,
                "achievedAt": float(row[6]),
                "hasReplay": bool(row[7]) or (str(row[0]), str(row[1])) in replay_keys,
            }
            for row in rows
        ]

    def dashboard_player_stats(self) -> list[dict[str, object]]:
        """Return durable cumulative totals for authenticated racing profiles."""
        rows = self.current_connection().execute(
            "SELECT identity_key, username, play_seconds, rubber_deaths, "
            "deathzone_deaths, finishes, distance_meters, turns, updated_at "
            "FROM player_stats WHERE authenticated=1 ORDER BY identity_key"
        ).fetchall()
        return [
            {
                "identityKey": str(row[0]),
                "username": str(row[1]),
                "playSeconds": round(max(0.0, float(row[2])), 3),
                "rubberDeaths": max(0, int(row[3])),
                "deathzoneDeaths": max(0, int(row[4])),
                "finishes": max(0, int(row[5])),
                "distanceMeters": round(max(0.0, float(row[6])), 3),
                "turns": max(0, int(row[7])),
                "updatedAt": int(float(row[8]) * 1000),
            }
            for row in rows
        ]

    def dashboard_replay_player_ids(self, map_key: str) -> set[str]:
        """Return public player ids with a viewable finished run on one map."""
        connection = self.current_connection()
        rows = connection.execute(
            "SELECT DISTINCT replay_players.identity_key FROM replay_runs "
            "JOIN replay_players ON replay_players.id=replay_runs.player_ref "
            "JOIN replay_maps ON replay_maps.id=replay_runs.map_ref WHERE "
            "replay_maps.record_key=? AND replay_runs.outcome=1 AND "
            "replay_runs.finish_seconds IS NOT NULL",
            (map_key,),
        ).fetchall()
        identities = {str(row[0]) for row in rows}
        identities.update(
            str(row[0]) for row in connection.execute(
                "SELECT identity_key FROM records WHERE map_key=? "
                "AND replay_available=1",
                (map_key,),
            ).fetchall()
        )
        return {public_player_id(identity) for identity in identities}

    def mark_replay_available(self, map_key: str, identity_key: str) -> bool:
        """Remember that some viewable run exists for this racer and map."""
        with self.connection:
            cursor = self.connection.execute(
                "UPDATE records SET replay_available=1 WHERE map_key=? AND "
                "identity_key=? AND authenticated=1 AND replay_available=0",
                (map_key, identity_key),
            )
        return int(cursor.rowcount) > 0

    def dashboard_finished_replays_after(
        self,
        run_id: int,
        limit: int = 100,
    ) -> list[dict[str, object]]:
        """Return a bounded queue of finished replay captures for publishing."""
        rows = self.current_connection().execute(
            "SELECT replay_runs.id, replay_players.identity_key, "
            "replay_players.username, replay_players.authenticated, "
            "replay_maps.map_identifier, replay_maps.revision_identifier, "
            "replay_maps.record_key, replay_maps.resource_key, "
            "replay_maps.storage_path, replay_runs.recorded_at, "
            "replay_runs.ended_at, replay_runs.finish_seconds, "
            "replay_runs.finish_turns, replay_runs.personal_best, "
            "replay_runs.event_count, replay_runs.settings_ref "
            "FROM replay_runs JOIN replay_players ON "
            "replay_players.id=replay_runs.player_ref JOIN replay_maps ON "
            "replay_maps.id=replay_runs.map_ref WHERE replay_runs.id>? "
            "AND replay_runs.outcome=1 AND replay_runs.finish_seconds IS NOT NULL "
            "ORDER BY replay_runs.id LIMIT ?",
            (max(0, int(run_id)), max(1, min(int(limit), 500))),
        ).fetchall()
        return [
            {
                "runId": int(row[0]),
                "identityKey": str(row[1]),
                "playerId": public_player_id(str(row[1])),
                "username": str(row[2]),
                "authenticated": bool(row[3]),
                "mapId": str(row[4]),
                "revisionId": str(row[5]),
                "mapKey": str(row[6]),
                "mapResourcePath": str(row[7]),
                "mapStoragePath": str(row[8]),
                "recordedAt": float(row[9]),
                "endedAt": float(row[10]),
                "seconds": float(row[11]),
                "turns": int(row[12]) if row[12] is not None else None,
                "personalBest": bool(row[13]),
                "eventCount": int(row[14]),
                "settingsRef": int(row[15]) if row[15] is not None else None,
            }
            for row in rows
        ]

    def dashboard_replay_history_groups_after(
        self,
        record_key: str = "",
        identity_key: str = "",
        limit: int = 20,
    ) -> list[dict[str, object]]:
        """Return stable player/map groups for metadata-only history backfills."""
        rows = self.current_connection().execute(
            "SELECT replay_maps.record_key, replay_players.identity_key, "
            "replay_players.username, replay_players.authenticated, "
            "MIN(replay_maps.map_identifier), MIN(replay_maps.revision_identifier) "
            "FROM replay_runs JOIN replay_players ON "
            "replay_players.id=replay_runs.player_ref JOIN replay_maps ON "
            "replay_maps.id=replay_runs.map_ref WHERE replay_runs.outcome=1 "
            "AND replay_runs.finish_seconds IS NOT NULL AND "
            "(replay_maps.record_key > ? OR (replay_maps.record_key=? AND "
            "replay_players.identity_key>?)) GROUP BY replay_maps.record_key, "
            "replay_players.identity_key ORDER BY replay_maps.record_key, "
            "replay_players.identity_key LIMIT ?",
            (
                record_key,
                record_key,
                identity_key,
                max(1, min(int(limit), 100)),
            ),
        ).fetchall()
        return [
            {
                "mapKey": str(row[0]),
                "identityKey": str(row[1]),
                "playerId": public_player_id(str(row[1])),
                "username": str(row[2]),
                "authenticated": bool(row[3]),
                "mapId": str(row[4]),
                "revisionId": str(row[5]),
            }
            for row in rows
        ]

    def dashboard_player_map_history(
        self,
        identity_key: str,
        map_key: str,
        limit: int = 2500,
    ) -> list[dict[str, object]]:
        rows = self.current_connection().execute(
            "SELECT replay_runs.id, replay_runs.recorded_at, "
            "replay_runs.ended_at, replay_runs.finish_seconds, "
            "replay_runs.finish_turns, replay_runs.personal_best, "
            "replay_runs.event_count, replay_runs.settings_ref, "
            "replay_maps.map_identifier, replay_maps.revision_identifier, "
            "replay_maps.resource_key, replay_maps.storage_path "
            "FROM replay_runs JOIN replay_players ON "
            "replay_players.id=replay_runs.player_ref JOIN replay_maps ON "
            "replay_maps.id=replay_runs.map_ref WHERE "
            "replay_players.identity_key=? AND replay_maps.record_key=? "
            "AND replay_runs.outcome=1 AND replay_runs.finish_seconds IS NOT NULL "
            "ORDER BY replay_runs.recorded_at DESC, replay_runs.id DESC LIMIT ?",
            (identity_key, map_key, max(1, min(int(limit), 2500))),
        ).fetchall()
        return [
            {
                "runId": int(row[0]),
                "recordedAt": int(float(row[1]) * 1000),
                "endedAt": int(float(row[2]) * 1000),
                "seconds": round(float(row[3]), 6),
                "turns": int(row[4]) if row[4] is not None else None,
                "personalBest": bool(row[5]),
                "eventCount": int(row[6]),
                "settingsRef": int(row[7]) if row[7] is not None else None,
                "mapId": str(row[8]),
                "revisionId": str(row[9]),
                "mapResourcePath": str(row[10]),
                "mapStoragePath": str(row[11]),
            }
            for row in rows
        ]

    def dashboard_replay_payload(self, run_id: int) -> dict[str, object] | None:
        connection = self.current_connection()
        row = connection.execute(
            "SELECT replay_runs.id, replay_players.identity_key, "
            "replay_players.username, replay_players.authenticated, "
            "replay_maps.map_identifier, replay_maps.revision_identifier, "
            "replay_maps.resource_key, replay_runs.recorded_at, "
            "replay_runs.ended_at, replay_runs.spawn_game_time, "
            "replay_runs.release_offset_us, replay_runs.start_x, "
            "replay_runs.start_y, replay_runs.start_xdir, "
            "replay_runs.start_ydir, replay_runs.start_speed, "
            "replay_runs.initial_turns, replay_runs.size_factor, "
            "replay_runs.start_mode, replay_runs.checkpoint_spawn, "
            "replay_runs.settings_ref, replay_runs.finish_seconds, "
            "replay_runs.finish_turns, replay_runs.personal_best, "
            "replay_runs.format_version, replay_runs.input_data "
            "FROM replay_runs JOIN replay_players ON "
            "replay_players.id=replay_runs.player_ref JOIN replay_maps ON "
            "replay_maps.id=replay_runs.map_ref WHERE replay_runs.id=? "
            "AND replay_runs.outcome=1 AND replay_runs.finish_seconds IS NOT NULL",
            (int(run_id),),
        ).fetchone()
        if row is None:
            return None
        events = decode_replay_inputs(bytes(row[25]))
        transitions = connection.execute(
            "SELECT replay_setting_transitions.offset_us, replay_settings.fingerprint_sha256 "
            "FROM replay_setting_transitions JOIN replay_settings ON "
            "replay_settings.id=replay_setting_transitions.settings_ref "
            "WHERE replay_setting_transitions.run_ref=? ORDER BY "
            "replay_setting_transitions.offset_us",
            (int(run_id),),
        ).fetchall()
        settings_fingerprint = ""
        if row[20] is not None:
            settings_row = connection.execute(
                "SELECT fingerprint_sha256 FROM replay_settings WHERE id=?",
                (int(row[20]),),
            ).fetchone()
            settings_fingerprint = str(settings_row[0]) if settings_row else ""
        return {
            "schemaVersion": 1,
            "formatVersion": int(row[24]),
            "runId": int(row[0]),
            "playerId": public_player_id(str(row[1])),
            "name": str(row[2])[:128],
            "authenticated": bool(row[3]),
            "mapId": str(row[4]),
            "revisionId": str(row[5]),
            "mapKey": str(row[6]),
            "recordedAt": int(float(row[7]) * 1000),
            "endedAt": int(float(row[8]) * 1000),
            "spawnGameTime": round(float(row[9]), 6),
            "releaseOffsetUs": int(row[10]) if row[10] is not None else None,
            "start": {
                "x": round(float(row[11]), 9),
                "y": round(float(row[12]), 9),
                "xdir": round(float(row[13]), 12),
                "ydir": round(float(row[14]), 12),
                "speed": round(float(row[15]), 9),
                "turns": int(row[16]),
                "sizeFactor": float(row[17]) if row[17] is not None else None,
                "mode": int(row[18]),
                "checkpoint": bool(row[19]),
            },
            "settingsFingerprint": settings_fingerprint,
            "settingsTransitions": [
                [int(offset), str(fingerprint)]
                for offset, fingerprint in transitions
            ],
            "seconds": round(float(row[21]), 6),
            "turns": int(row[22]) if row[22] is not None else None,
            "personalBest": bool(row[23]),
            "events": [[int(offset), int(action)] for offset, action in events],
        }

    def dashboard_replay_settings(self, settings_ref: int) -> dict[str, object] | None:
        row = self.current_connection().execute(
            "SELECT fingerprint_sha256, format_version, setting_count, "
            "compression, setting_data FROM replay_settings WHERE id=?",
            (int(settings_ref),),
        ).fetchone()
        if row is None:
            return None
        raw = zlib.decompress(bytes(row[4])) if int(row[3]) == 1 else bytes(row[4])
        items = decode_replay_settings(raw)
        return {
            "schemaVersion": 1,
            "formatVersion": int(row[1]),
            "fingerprint": str(row[0]),
            "settingCount": int(row[2]),
            "settings": [
                [name.decode("utf-8", "replace"), value.decode("utf-8", "replace")]
                for name, value in items
            ],
        }

    def dashboard_replay_settings_by_fingerprint(
        self,
        fingerprint: str,
    ) -> dict[str, object] | None:
        row = self.current_connection().execute(
            "SELECT id FROM replay_settings WHERE fingerprint_sha256=?",
            (str(fingerprint),),
        ).fetchone()
        return self.dashboard_replay_settings(int(row[0])) if row else None









    def rating_average(self, map_key: str) -> float | None:
        row = self.connection.execute(
            "SELECT AVG(rating) FROM ratings WHERE map_key=?", (map_key,)
        ).fetchone()
        return float(row[0]) if row and row[0] is not None else None

    def rating_summary(self, map_key: str) -> tuple[float, int] | None:
        row = self.connection.execute(
            "SELECT AVG(rating), COUNT(*) FROM ratings WHERE map_key=?",
            (map_key,),
        ).fetchone()
        if not row or row[0] is None or int(row[1]) < 1:
            return None
        return float(row[0]), int(row[1])

    def rating_summaries(self) -> dict[str, tuple[float, int]]:
        """Return every map rating using one bounded aggregate query."""
        rows = self.current_connection().execute(
            "SELECT map_key, AVG(rating), COUNT(*) FROM ratings GROUP BY map_key"
        ).fetchall()
        return {
            str(row[0]): (float(row[1]), int(row[2]))
            for row in rows
            if row[1] is not None and int(row[2]) > 0
        }

    def rating_entries_by_map(
        self, per_map_limit: int = 500
    ) -> dict[str, list[dict[str, object]]]:
        """Return bounded current submissions for public per-map display."""
        limit = max(1, min(int(per_map_limit), 500))
        rows = self.current_connection().execute(
            "WITH ranked AS ("
            "SELECT map_key, identity_key, username, authenticated, rating, rated_at, "
            "ROW_NUMBER() OVER (PARTITION BY map_key "
            "ORDER BY rated_at DESC, identity_key ASC) AS position "
            "FROM ratings) "
            "SELECT map_key, identity_key, username, authenticated, rating, rated_at "
            "FROM ranked WHERE position <= ? ORDER BY map_key, rated_at DESC",
            (limit,),
        ).fetchall()
        result: dict[str, list[dict[str, object]]] = collections.defaultdict(list)
        for map_key, identity_key, username, authenticated, rating, rated_at in rows:
            result[str(map_key)].append({
                "playerId": public_player_id(str(identity_key)),
                "name": str(username)[:128],
                "authenticated": bool(authenticated),
                "racingProfile": str(identity_key).startswith("auth:"),
                "rating": int(rating),
                "ratedAt": int(float(rated_at) * 1000),
            })
        return dict(result)

    def rating_for(self, map_key: str, identity_key: str) -> int | None:
        row = self.connection.execute(
            "SELECT rating FROM ratings WHERE map_key=? AND identity_key=?",
            (map_key, identity_key),
        ).fetchone()
        return int(row[0]) if row else None

    def set_rating(
        self, map_key: str, player: Player, rating: int
    ) -> tuple[int | None, bool]:
        return self.set_rating_identity(
            map_key,
            player.identity_key,
            player.record_name,
            bool(player.auth_name),
            rating,
        )

    def set_rating_identity(
        self,
        map_key: str,
        identity_key: str,
        username: str,
        authenticated: bool,
        rating: int,
        *,
        rated_at: float | None = None,
    ) -> tuple[int | None, bool]:
        if not 1 <= rating <= 5:
            raise ValueError("rating must be between 1 and 5")
        if (
            not map_key
            or len(map_key) > 1024
            or not identity_key
            or len(identity_key) > 512
            or any(
                ord(character) < 32 or ord(character) == 127
                for character in map_key + identity_key
            )
        ):
            raise ValueError("invalid rating identity")
        clean_username = "".join(
            " " if ord(character) < 32 or ord(character) == 127 else character
            for character in str(username)
        ).strip()[:128]
        if not clean_username:
            clean_username = "Racer"
        previous = self.rating_for(map_key, identity_key)
        now = time.time() if rated_at is None else float(rated_at)
        if not math.isfinite(now) or now <= 0:
            raise ValueError("invalid rating timestamp")
        if previous == rating:
            with self.connection:
                self.connection.execute(
                    "UPDATE ratings SET username=?, authenticated=?, rated_at=? "
                    "WHERE map_key=? AND identity_key=?",
                    (
                        clean_username,
                        int(bool(authenticated)),
                        now,
                        map_key,
                        identity_key,
                    ),
                )
            return previous, False
        with self.connection:
            self.connection.execute(
                "INSERT INTO ratings("
                "map_key, identity_key, username, authenticated, rating, "
                "previous_rating, undo_available, rated_at) "
                "VALUES(?, ?, ?, ?, ?, ?, 1, ?) "
                "ON CONFLICT(map_key, identity_key) DO UPDATE SET "
                "username=excluded.username, "
                "authenticated=excluded.authenticated, "
                "rating=excluded.rating, "
                "previous_rating=excluded.previous_rating, "
                "undo_available=1, "
                "rated_at=excluded.rated_at",
                (
                    map_key,
                    identity_key,
                    clean_username,
                    int(bool(authenticated)),
                    rating,
                    previous,
                    now,
                ),
            )
        return previous, True

    def undo_rating(
        self, map_key: str, identity_key: str
    ) -> tuple[int, int | None] | None:
        row = self.connection.execute(
            "SELECT rating, previous_rating, undo_available FROM ratings "
            "WHERE map_key=? AND identity_key=?",
            (map_key, identity_key),
        ).fetchone()
        if not row or not bool(row[2]):
            return None
        current = int(row[0])
        previous = int(row[1]) if row[1] is not None else None
        with self.connection:
            if previous is None:
                self.connection.execute(
                    "DELETE FROM ratings WHERE map_key=? AND identity_key=?",
                    (map_key, identity_key),
                )
            else:
                self.connection.execute(
                    "UPDATE ratings SET rating=?, previous_rating=NULL, "
                    "undo_available=0, rated_at=? "
                    "WHERE map_key=? AND identity_key=?",
                    (previous, time.time(), map_key, identity_key),
                )
        return current, previous

    def revoke_rating(self, map_key: str, identity_key: str) -> int | None:
        current = self.rating_for(map_key, identity_key)
        if current is None:
            return None
        with self.connection:
            self.connection.execute(
                "DELETE FROM ratings WHERE map_key=? AND identity_key=?",
                (map_key, identity_key),
            )
        return current

    def reset_map(self, map_key: str) -> tuple[int, int]:
        record_count = self.connection.execute(
            "SELECT COUNT(*) FROM records WHERE map_key=?", (map_key,)
        ).fetchone()[0]
        finish_count = self.connection.execute(
            "SELECT COUNT(*) FROM finishes WHERE map_key=?", (map_key,)
        ).fetchone()[0]
        with self.connection:
            self.connection.execute("DELETE FROM records WHERE map_key=?", (map_key,))
            self.connection.execute("DELETE FROM finishes WHERE map_key=?", (map_key,))
        return int(record_count), int(finish_count)

    def reset_user(self, map_key: str, username: str) -> tuple[list[str], int, int]:
        query = plain_console_text(username).strip().casefold()
        if not query:
            return [], 0, 0
        rows = self.connection.execute(
            "SELECT identity_key, username FROM records WHERE map_key=? "
            "UNION SELECT identity_key, username FROM finishes WHERE map_key=?",
            (map_key, map_key),
        ).fetchall()
        identities: set[str] = set()
        names: set[str] = set()
        for identity_key, stored_name in rows:
            identity_fold = str(identity_key).casefold()
            identity_name = identity_fold.split(":", 1)[-1]
            if query in {
                identity_fold,
                identity_name,
                plain_console_text(stored_name).casefold(),
            }:
                identities.add(str(identity_key))
                names.add(str(stored_name))
        if not identities:
            return [], 0, 0
        placeholders = ",".join("?" for _ in identities)
        parameters = [map_key, *sorted(identities)]
        record_count = self.connection.execute(
            f"SELECT COUNT(*) FROM records WHERE map_key=? "
            f"AND identity_key IN ({placeholders})",
            parameters,
        ).fetchone()[0]
        finish_count = self.connection.execute(
            f"SELECT COUNT(*) FROM finishes WHERE map_key=? "
            f"AND identity_key IN ({placeholders})",
            parameters,
        ).fetchone()[0]
        with self.connection:
            self.connection.execute(
                f"DELETE FROM records WHERE map_key=? "
                f"AND identity_key IN ({placeholders})",
                parameters,
            )
            self.connection.execute(
                f"DELETE FROM finishes WHERE map_key=? "
                f"AND identity_key IN ({placeholders})",
                parameters,
            )
        return sorted(names, key=str.casefold), int(record_count), int(finish_count)

    def matching_user_identities(self, username: str) -> list[StoredIdentity]:
        """Find saved-time identities without silently merging ambiguous users."""
        query = plain_console_text(username).strip().casefold()
        if not query:
            return []
        rows = self.connection.execute(
            "SELECT identity_key, username, authenticated, saved_at FROM ("
            "SELECT identity_key, username, authenticated, achieved_at AS saved_at "
            "FROM records UNION ALL "
            "SELECT identity_key, username, authenticated, finished_at AS saved_at "
            "FROM finishes UNION ALL "
            "SELECT replay_players.identity_key, replay_players.username, "
            "replay_players.authenticated, MAX(replay_runs.recorded_at) AS saved_at "
            "FROM replay_players JOIN replay_runs "
            "ON replay_runs.player_ref=replay_players.id "
            "GROUP BY replay_players.id) ORDER BY saved_at DESC"
        ).fetchall()
        identities: dict[str, StoredIdentity] = {}
        direct_matches: set[str] = set()
        name_matches: set[str] = set()
        explicit_identity = query.startswith(("auth:", "guest:"))
        for identity_key, stored_name, authenticated, _ in rows:
            identity_key = str(identity_key)
            identity_fold = identity_key.casefold()
            identity = identities.setdefault(
                identity_fold,
                StoredIdentity(identity_key, str(stored_name), bool(authenticated)),
            )
            if query == identity_fold or (
                not explicit_identity and query == identity_fold.split(":", 1)[-1]
            ):
                direct_matches.add(identity.identity_key.casefold())
            if (
                not explicit_identity
                and query == plain_console_text(stored_name).strip().casefold()
            ):
                name_matches.add(identity.identity_key.casefold())
        selected = direct_matches if direct_matches else name_matches
        return sorted(
            (identities[key] for key in selected),
            key=lambda identity: identity.identity_key.casefold(),
        )

    @staticmethod
    def identity_for_player(player: Player) -> StoredIdentity:
        return StoredIdentity(
            player.identity_key,
            player.record_name,
            bool(player.auth_name),
        )

    @staticmethod
    def explicit_user_identity(username: str) -> StoredIdentity | None:
        explicit = plain_console_text(username).strip()
        explicit_fold = explicit.casefold()
        if explicit_fold.startswith("auth:"):
            return StoredIdentity(
                explicit_fold,
                explicit.split(":", 1)[1],
                True,
            )
        if explicit_fold.startswith("guest:"):
            return StoredIdentity(
                explicit_fold,
                explicit.split(":", 1)[1],
                False,
            )
        return None

    def merge_users(
        self,
        source_identity_key: str,
        destination: StoredIdentity,
    ) -> UserMergeResult:
        """Atomically move all times, finishes, and replays to ``destination``."""
        if source_identity_key.casefold() == destination.identity_key.casefold():
            raise ValueError("source and destination identities are the same")
        source_records = self.connection.execute(
            "SELECT map_key, best_seconds, best_turns, achieved_at FROM records "
            "WHERE identity_key=?",
            (source_identity_key,),
        ).fetchall()
        finish_count = int(
            self.connection.execute(
                "SELECT COUNT(*) FROM finishes WHERE identity_key=?",
                (source_identity_key,),
            ).fetchone()[0]
        )
        source_replay_player = self.connection.execute(
            "SELECT id FROM replay_players WHERE identity_key=?",
            (source_identity_key,),
        ).fetchone()
        replay_count = 0
        if source_replay_player is not None:
            replay_count = int(
                self.connection.execute(
                    "SELECT COUNT(*) FROM replay_runs WHERE player_ref=?",
                    (source_replay_player[0],),
                ).fetchone()[0]
            )
        overlapping_records = 0
        with self.connection:
            for map_key, seconds, turns, achieved_at in source_records:
                existing = self.connection.execute(
                    "SELECT best_seconds, best_turns FROM records "
                    "WHERE map_key=? AND identity_key=?",
                    (map_key, destination.identity_key),
                ).fetchone()
                source_rank = (
                    float(seconds),
                    math.inf if turns is None else int(turns),
                )
                if existing is None:
                    self.connection.execute(
                        "INSERT INTO records("
                        "map_key, identity_key, username, authenticated, "
                        "best_seconds, best_turns, achieved_at) "
                        "VALUES(?, ?, ?, ?, ?, ?, ?)",
                        (
                            map_key,
                            destination.identity_key,
                            destination.username,
                            int(destination.authenticated),
                            seconds,
                            turns,
                            achieved_at,
                        ),
                    )
                else:
                    overlapping_records += 1
                    destination_rank = (
                        float(existing[0]),
                        math.inf if existing[1] is None else int(existing[1]),
                    )
                    if source_rank < destination_rank:
                        self.connection.execute(
                            "UPDATE records SET username=?, authenticated=?, "
                            "best_seconds=?, best_turns=?, achieved_at=? "
                            "WHERE map_key=? AND identity_key=?",
                            (
                                destination.username,
                                int(destination.authenticated),
                                seconds,
                                turns,
                                achieved_at,
                                map_key,
                                destination.identity_key,
                            ),
                        )
                    else:
                        self.connection.execute(
                            "UPDATE records SET username=?, authenticated=? "
                            "WHERE map_key=? AND identity_key=?",
                            (
                                destination.username,
                                int(destination.authenticated),
                                map_key,
                                destination.identity_key,
                            ),
                        )
            self.connection.execute(
                "UPDATE finishes SET identity_key=?, username=?, authenticated=? "
                "WHERE identity_key=?",
                (
                    destination.identity_key,
                    destination.username,
                    int(destination.authenticated),
                    source_identity_key,
                ),
            )
            self.connection.execute(
                "DELETE FROM records WHERE identity_key=?",
                (source_identity_key,),
            )
            if source_replay_player is not None:
                self.connection.execute(
                    "INSERT INTO replay_players(identity_key, username, authenticated) "
                    "VALUES(?, ?, ?) ON CONFLICT(identity_key) DO UPDATE SET "
                    "username=excluded.username, authenticated=excluded.authenticated",
                    (
                        destination.identity_key,
                        destination.username,
                        int(destination.authenticated),
                    ),
                )
                destination_replay_player = self.connection.execute(
                    "SELECT id FROM replay_players WHERE identity_key=?",
                    (destination.identity_key,),
                ).fetchone()[0]
                self.connection.execute(
                    "UPDATE replay_runs SET player_ref=? WHERE player_ref=?",
                    (destination_replay_player, source_replay_player[0]),
                )
                self.connection.execute(
                    "DELETE FROM replay_players WHERE id=?",
                    (source_replay_player[0],),
                )
            source_stats = self.connection.execute(
                "SELECT play_seconds, rubber_deaths, deathzone_deaths, finishes, "
                "distance_meters, turns, updated_at FROM player_stats "
                "WHERE identity_key=?",
                (source_identity_key,),
            ).fetchone()
            if source_stats is not None:
                self._increment_player_stats(
                    destination.identity_key,
                    destination.username,
                    destination.authenticated,
                    play_seconds=float(source_stats[0]),
                    rubber_deaths=int(source_stats[1]),
                    deathzone_deaths=int(source_stats[2]),
                    finishes=int(source_stats[3]),
                    distance_meters=float(source_stats[4]),
                    turns=int(source_stats[5]),
                    updated_at=float(source_stats[6]),
                )
                self.connection.execute(
                    "DELETE FROM player_stats WHERE identity_key=?",
                    (source_identity_key,),
                )
        return UserMergeResult(
            records_moved=len(source_records),
            finishes_moved=finish_count,
            overlapping_records=overlapping_records,
            replay_runs_moved=replay_count,
        )


@dataclasses.dataclass(frozen=True)
class HotCommandDefinition:
    command: str
    handler: object
    access_setting: str
    access_denied: str
    help_command: str
    help_description: str


class HotCommandRegistry:
    """Atomically reload standalone admin command modules when files change."""

    def __init__(self, directory: Path):
        self.directory = directory
        self._commands: dict[str, HotCommandDefinition] = {}
        self._last_attempted_fingerprint: tuple[tuple[str, str], ...] | None = None
        self.last_error: str | None = None

    def _snapshot(
        self,
    ) -> tuple[tuple[tuple[str, str], ...], tuple[tuple[Path, bytes], ...]]:
        if not self.directory.is_dir():
            return (), ()
        files = tuple(
            (path, path.read_bytes())
            for path in sorted(self.directory.glob("*.py"))
            if not path.name.startswith("_")
        )
        fingerprint = tuple(
            (path.name, hashlib.sha256(source).hexdigest())
            for path, source in files
        )
        return fingerprint, files

    def reload_if_changed(self) -> bool:
        try:
            fingerprint, files = self._snapshot()
        except OSError as exc:
            self.last_error = str(exc)
            LOG.exception("reading hot command modules failed")
            return False
        if fingerprint == self._last_attempted_fingerprint:
            return False
        self._last_attempted_fingerprint = fingerprint
        candidate: dict[str, HotCommandDefinition] = {}
        try:
            for path, source in files:
                namespace = {
                    "__builtins__": __builtins__,
                    "__file__": str(path),
                    "__name__": f"_tronner_hot_command_{path.stem}",
                }
                exec(compile(source, str(path), "exec"), namespace)
                declarations = namespace.get("COMMANDS")
                if not isinstance(declarations, dict):
                    raise TypeError(f"{path.name} must define a COMMANDS dictionary")
                for raw_command, metadata in declarations.items():
                    command = str(raw_command).strip().casefold()
                    if not command.startswith("/") or any(
                        character.isspace() for character in command
                    ):
                        raise ValueError(
                            f"invalid command name {raw_command!r} in {path.name}"
                        )
                    if command in candidate:
                        raise ValueError(f"duplicate hot command: {command}")
                    if not isinstance(metadata, dict):
                        raise TypeError(f"metadata for {command} must be a dictionary")
                    handler = metadata.get("handler")
                    if not callable(handler):
                        raise TypeError(f"handler for {command} is not callable")
                    candidate[command] = HotCommandDefinition(
                        command=command,
                        handler=handler,
                        access_setting=str(metadata["access_setting"]),
                        access_denied=str(metadata["access_denied"]),
                        help_command=str(metadata["help_command"]),
                        help_description=str(metadata["help_description"]),
                    )
        except Exception as exc:
            self.last_error = f"{type(exc).__name__}: {exc}"
            LOG.exception(
                "hot command reload failed; retaining %d last-known-good command(s)",
                len(self._commands),
            )
            return False
        self._commands = candidate
        self.last_error = None
        LOG.info(
            "loaded %d hot admin command(s) from %s",
            len(candidate),
            self.directory,
        )
        return True

    async def dispatch(
        self,
        controller,
        command: str,
        player: Player,
        access_level: int,
        arguments: str,
    ) -> bool:
        self.reload_if_changed()
        definition = self._commands.get(command.casefold())
        if definition is None:
            return False
        maximum_access = int(controller.config.get(definition.access_setting, 1))
        if access_level > maximum_access:
            await controller.private(player, definition.access_denied)
            return True
        await definition.handler(controller, player, access_level, arguments)
        return True

    def help_entries(
        self, config: dict, access_level: int
    ) -> list[tuple[str, str]]:
        return [
            (definition.help_command, definition.help_description)
            for definition in sorted(
                self._commands.values(), key=lambda item: item.command
            )
            if access_level <= int(config.get(definition.access_setting, 1))
        ]


class CommandSink:
    def __init__(self, path: Path, encoding: str = "utf-8"):
        self.path = path
        self.encoding = canonical_game_text_encoding(encoding, "utf-8")
        self.lock = asyncio.Lock()

    def set_encoding(self, encoding: str) -> None:
        self.encoding = canonical_game_text_encoding(encoding, self.encoding)

    async def send(self, *commands: str) -> None:
        lines = []
        for command in commands:
            # Preserve intentional trailing whitespace in CENTER_MESSAGE while
            # still guaranteeing one physical console command per item.
            command = str(command).replace("\r", " ").replace("\n", " ")
            if command.strip():
                lines.append(command)
        if not lines:
            return
        payload = encode_game_text(
            "\n".join(lines) + "\n",
            self.encoding,
            "Armagetron console command",
        )
        async with self.lock:
            fd = os.open(self.path, os.O_WRONLY | os.O_APPEND)
            try:
                os.write(fd, payload)
            finally:
                os.close(fd)


class MapRepository:
    PARSED_CATALOG_CACHE_SCHEMA = 1

    def __init__(self, config: dict):
        self.source = str(config.get("repository_source", "git")).strip().casefold()
        if self.source not in {"git", "firebase"}:
            raise ValueError("repository_source must be git or firebase")
        self.git_url = config["repository_git_url"]
        self.branch = config.get("repository_branch", "main")
        self.git_checkout = Path(config["repository_checkout"])
        self.firebase_root = Path(
            config.get(
                "firebase_catalog_dir",
                "/var/lib/tronner-racing/firebase-catalog",
            )
        )
        self.checkout = (
            self.firebase_root / "current"
            if self.source == "firebase"
            else self.git_checkout
        )
        self.firebase = (
            FirebaseCatalogClient(config) if self.source == "firebase" else None
        )
        self.firebase_require_ready = bool(
            config.get("firebase_catalog_require_ready", True)
        )
        self.firebase_publish_wait_seconds = max(
            5.0,
            float(config.get("firebase_catalog_publish_wait_seconds", 60)),
        )
        self.firebase_maps_by_key: dict[str, dict] = {}
        self.firebase_inactive_keys: set[str] = set()
        self.firebase_generation = ""
        self.firebase_catalog_version = 0
        self.public_dir = Path(config["public_dir"])
        self.cache_dir = Path(config["resource_cache_dir"])
        self.dtd_source_dir = Path(config["dtd_source_dir"])
        self.override_dir = Path(
            config.get("map_override_dir", "/var/lib/tronner-racing/map-overrides")
        )
        self.revision_dir = Path(
            config.get(
                "map_revision_dir",
                "/var/lib/tronner-racing/map-revisions",
            )
        )
        self.excluded_keys: set[str] = set()
        self.catalog: dict[str, MapEntry] = {}
        self.source_to_key: dict[str, str] = {}
        self.issues: list[str] = []
        self._ghost_geometry_cache: dict[
            tuple[str, int, int, float], tuple | None
        ] = {}

    def _parsed_catalog_cache_path(self) -> Path | None:
        generation = self.firebase_generation
        if self.firebase is None or not re.fullmatch(r"[A-Za-z0-9._-]{1,128}", generation):
            return None
        return self.firebase_root / "parsed-catalog" / f"{generation}.json"

    @staticmethod
    def _cached_entry(entry: MapEntry) -> dict[str, object]:
        return {
            "key": entry.key,
            "name": entry.name,
            "author": entry.author,
            "version": entry.version,
            "category": entry.category,
            "sourcePath": entry.source_path,
            "spawns": [dataclasses.asdict(spawn) for spawn in entry.spawns],
            "axes": entry.axes,
            "mapId": entry.map_id,
            "revisionId": entry.revision_id,
            "storagePath": entry.storage_path,
            "recordKey": entry.record_key,
            "ratingKey": entry.rating_key_override,
            "checkpointIds": list(entry.checkpoint_ids),
            "checkpointMode": entry.checkpoint_mode,
            "timeDecimals": entry.time_decimals,
        }

    def _write_parsed_catalog_cache(self) -> None:
        path = self._parsed_catalog_cache_path()
        if path is None:
            return
        payload = {
            "schemaVersion": self.PARSED_CATALOG_CACHE_SCHEMA,
            "generation": self.firebase_generation,
            "catalogVersion": self.firebase_catalog_version,
            "excludedKeys": sorted(self.excluded_keys),
            "entries": [
                self._cached_entry(entry)
                for entry in sorted(self.catalog.values(), key=lambda item: item.key)
            ],
            "sourceToKey": self.source_to_key,
            "issues": self.issues,
        }
        path.parent.mkdir(parents=True, exist_ok=True)
        temporary = path.with_name(f".{path.name}.{os.getpid()}.tmp")
        try:
            with temporary.open("x", encoding="utf-8") as handle:
                json.dump(payload, handle, ensure_ascii=False, separators=(",", ":"))
                handle.write("\n")
                handle.flush()
                os.fsync(handle.fileno())
            os.replace(temporary, path)
        finally:
            with contextlib.suppress(FileNotFoundError):
                temporary.unlink()

    def _load_parsed_catalog_cache(self) -> bool:
        path = self._parsed_catalog_cache_path()
        if path is None or not path.is_file():
            return False
        try:
            payload = json.loads(path.read_text("utf-8"))
            if (
                payload.get("schemaVersion") != self.PARSED_CATALOG_CACHE_SCHEMA
                or payload.get("generation") != self.firebase_generation
                or int(payload.get("catalogVersion") or 0)
                != self.firebase_catalog_version
                or payload.get("excludedKeys") != sorted(self.excluded_keys)
                or not isinstance(payload.get("entries"), list)
            ):
                return False
            catalog: dict[str, MapEntry] = {}
            for item in payload["entries"]:
                source_path = str(item["sourcePath"])
                local_path = self.checkout / source_path
                key = str(item["key"])
                if not local_path.is_file() or not (self.public_dir / key).is_file():
                    return False
                entry = MapEntry(
                    key=key,
                    name=str(item["name"]),
                    author=str(item["author"]),
                    version=str(item["version"]),
                    category=str(item.get("category") or ""),
                    source_path=source_path,
                    local_path=local_path,
                    spawns=tuple(
                        SpawnPoint(
                            float(spawn["x"]),
                            float(spawn["y"]),
                            float(spawn["xdir"]),
                            float(spawn["ydir"]),
                        )
                        for spawn in item["spawns"]
                    ),
                    axes=(int(item["axes"]) if item.get("axes") is not None else None),
                    map_id=str(item.get("mapId") or ""),
                    revision_id=str(item.get("revisionId") or ""),
                    storage_path=str(item.get("storagePath") or ""),
                    record_key=str(item.get("recordKey") or ""),
                    rating_key_override=str(item.get("ratingKey") or ""),
                    checkpoint_ids=tuple(int(value) for value in item.get("checkpointIds", [])),
                    checkpoint_mode=str(item.get("checkpointMode") or ""),
                    time_decimals=int(item.get("timeDecimals", 3)),
                )
                if entry.key in catalog or not entry.spawns:
                    return False
                catalog[entry.key] = entry
            source_to_key = payload.get("sourceToKey")
            issues = payload.get("issues")
            if not catalog or not isinstance(source_to_key, dict) or not isinstance(issues, list):
                return False
            self.catalog = catalog
            self.source_to_key = {
                str(source): str(key) for source, key in source_to_key.items()
            }
            self.issues = [str(issue) for issue in issues]
        except (KeyError, OSError, TypeError, ValueError, json.JSONDecodeError):
            LOG.exception("unable to load parsed Firebase catalog cache %s", path)
            return False
        LOG.info(
            "loaded %d maps from local parsed catalog cache (generation %s)",
            len(self.catalog),
            self.firebase_generation,
        )
        return True

    def load_local_snapshot(self) -> None:
        """Load the already-validated immutable Firebase snapshot without networking."""
        if self.firebase is None:
            self.scan()
            return
        self._load_firebase_manifest()
        if not self._load_parsed_catalog_cache():
            self.scan()

    def local_catalog_signature(self) -> tuple[int, str, str] | None:
        if self.firebase is None:
            return None
        try:
            manifest = json.loads(
                (self.checkout / ".catalog.json").read_text("utf-8")
            )
        except (OSError, json.JSONDecodeError):
            return None
        signature = (
            int(manifest.get("catalogVersion") or 0),
            str(manifest.get("generation") or ""),
            str(manifest.get("sourceManifestSha256") or ""),
        )
        return signature if all(signature) else None

    def sync(
        self,
        restore_worktree: bool = False,
        *,
        catalog_state: dict | None = None,
        force_firestore: bool = False,
    ) -> dict | None:
        if self.firebase is not None:
            manifest = self.firebase.sync_snapshot(
                self.firebase_root,
                require_ready=self.firebase_require_ready,
                catalog_state=catalog_state,
                force_firestore=force_firestore,
            )
            self._load_firebase_manifest()
            self.scan()
            return manifest
        self.checkout.parent.mkdir(parents=True, exist_ok=True)
        if (self.checkout / ".git").is_dir():
            if restore_worktree:
                subprocess.run(
                    [
                        "git",
                        "-C",
                        str(self.checkout),
                        "restore",
                        "--source=HEAD",
                        "--worktree",
                        "--",
                        ".",
                    ],
                    check=True,
                    timeout=30,
                    stdout=subprocess.DEVNULL,
                    stderr=subprocess.PIPE,
                    text=True,
                )
            subprocess.run(
                ["git", "-C", str(self.checkout), "pull", "--ff-only", "origin", self.branch],
                check=True,
                timeout=90,
                stdout=subprocess.DEVNULL,
                stderr=subprocess.PIPE,
                text=True,
            )
        else:
            subprocess.run(
                ["git", "clone", "--depth", "1", "--branch", self.branch, self.git_url, str(self.checkout)],
                check=True,
                timeout=120,
                stdout=subprocess.DEVNULL,
                stderr=subprocess.PIPE,
                text=True,
            )
        self.scan()
        return None

    def _load_firebase_manifest(self) -> None:
        if self.firebase is None:
            self.firebase_maps_by_key = {}
            self.firebase_inactive_keys = set()
            return
        manifest_path = self.checkout / ".catalog.json"
        try:
            manifest = json.loads(manifest_path.read_text("utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            raise FirebaseCatalogError(
                f"unable to read Firebase catalog manifest: {exc}"
            ) from exc
        maps = manifest.get("maps", [])
        if not isinstance(maps, list) or not maps:
            raise FirebaseCatalogError("Firebase catalog manifest contains no maps")
        self.firebase_maps_by_key = {
            str(item["resourcePath"]): item
            for item in maps
            if isinstance(item, dict) and item.get("resourcePath")
        }
        self.firebase_inactive_keys = {
            key
            for key, item in self.firebase_maps_by_key.items()
            if item.get("status") != "active"
        }
        self.firebase_generation = str(manifest.get("generation") or "")
        self.firebase_catalog_version = int(manifest.get("catalogVersion") or 0)

    @staticmethod
    def _direction(node: ET.Element, inherited: tuple[float, float] | None = None) -> tuple[float, float]:
        if "angle" in node.attrib:
            angle = math.radians(float(node.attrib["angle"]))
            length = float(node.attrib.get("length", "1"))
            return math.cos(angle) * length, math.sin(angle) * length
        xdir = float(node.attrib.get("xdir", "0"))
        ydir = float(node.attrib.get("ydir", "0"))
        if xdir == 0 and ydir == 0 and inherited is not None:
            return inherited
        return xdir, ydir

    def _parse_map(self, path: Path, source_path: str | None = None) -> MapEntry:
        document = ET.parse(path)
        root = document.getroot()
        resource = root if local_name(root.tag) == "Resource" else next(
            node for node in root.iter() if local_name(node.tag) == "Resource"
        )
        author = resource.attrib["author"].strip()
        name = resource.attrib["name"].strip()
        version = resource.attrib["version"].strip()
        category = resource.attrib.get("category", "").strip("/")
        category_parts = [part for part in category.split("/") if part]
        for component in [author, name, version, *category_parts]:
            if not safe_resource_component(component):
                raise ValueError(f"unsafe resource component {component!r}")
        key = "/".join([author, *category_parts, f"{name}-{version}{MAP_SUFFIX}"])
        spawns: list[SpawnPoint] = []
        axes: int | None = None
        checkpoint_ids: set[int] = set()
        checkpoint_requirement: int | None = None
        time_decimals = 3
        for node in root.iter():
            if local_name(node.tag) == "Axes" and "number" in node.attrib:
                axes = int(node.attrib["number"])
                if axes < 1:
                    raise ValueError("map axes must be positive")
                break
        for node in root.iter():
            if (
                local_name(node.tag) == "Setting"
                and node.attrib.get("name", "").casefold()
                == "race_checkpoint_require_hit"
            ):
                try:
                    checkpoint_requirement = int(node.attrib.get("value", ""))
                except ValueError:
                    checkpoint_requirement = None
            if (
                local_name(node.tag) == "Setting"
                and node.attrib.get("name", "").casefold()
                == "race_time_decimals"
            ):
                try:
                    configured_decimals = int(node.attrib.get("value", ""))
                except ValueError as exc:
                    raise ValueError("RACE_TIME_DECIMALS must be an integer") from exc
                if not 0 <= configured_decimals <= 8:
                    raise ValueError("RACE_TIME_DECIMALS must be between 0 and 8")
                time_decimals = configured_decimals
            if (
                local_name(node.tag) == "Zone"
                and node.attrib.get("effect", "").casefold() == "checkpoint"
            ):
                checkpoint = next(
                    (
                        child
                        for child in node.iter()
                        if local_name(child.tag) == "Checkpoint"
                    ),
                    None,
                )
                if checkpoint is None:
                    raise ValueError("checkpoint zone has no Checkpoint element")
                try:
                    checkpoint_id = int(checkpoint.attrib["id"])
                except (KeyError, ValueError) as exc:
                    raise ValueError("checkpoint ID must be a positive integer") from exc
                if checkpoint_id <= 0:
                    raise ValueError("checkpoint ID must be a positive integer")
                checkpoint_ids.add(checkpoint_id)

        def add_spawn(node: ET.Element, inherited: tuple[float, float] | None = None) -> None:
            xdir, ydir = self._direction(node, inherited)
            spawns.append(
                SpawnPoint(float(node.attrib["x"]), float(node.attrib["y"]), xdir, ydir)
            )
            for child in node:
                if local_name(child.tag) == "Spawn":
                    add_spawn(child, (xdir, ydir))

        child_spawns = {
            id(child)
            for parent in root.iter()
            if local_name(parent.tag) == "Spawn"
            for child in parent
            if local_name(child.tag) == "Spawn"
        }
        for node in root.iter():
            if local_name(node.tag) == "Spawn" and id(node) not in child_spawns:
                add_spawn(node)
        if not spawns:
            raise ValueError("map has no spawn points")
        if source_path is None:
            source_path = path.relative_to(self.checkout).as_posix()
        firebase_metadata = self.firebase_maps_by_key.get(key, {})
        checkpoint_mode = ""
        if checkpoint_ids:
            checkpoint_mode = "unordered" if checkpoint_requirement == 1 else "ordered"
        return MapEntry(
            key=key,
            name=name,
            author=author,
            version=version,
            category=category,
            source_path=source_path,
            local_path=path,
            spawns=tuple(spawns),
            axes=axes,
            map_id=str(firebase_metadata.get("mapId", "")),
            revision_id=str(firebase_metadata.get("activeRevisionId", "")),
            storage_path=str(firebase_metadata.get("storagePath", "")),
            record_key=str(firebase_metadata.get("recordKey", "")),
            rating_key_override=str(firebase_metadata.get("ratingKey", "")),
            checkpoint_ids=tuple(sorted(checkpoint_ids)),
            checkpoint_mode=checkpoint_mode,
            time_decimals=time_decimals,
        )

    def scan(self) -> None:
        if self.firebase is not None:
            self._load_firebase_manifest()
        raw_catalog: dict[str, MapEntry] = {}
        source_to_raw_key: dict[str, str] = {}
        issues: list[str] = []
        roots = (
            ((self.checkout, False),)
            if self.firebase is not None
            else ((self.checkout, False), (self.override_dir, True))
        )
        for root, is_override in roots:
            if not root.is_dir():
                continue
            for path in sorted(root.rglob(f"*{MAP_SUFFIX}")):
                if ".git" in path.parts:
                    continue
                rel = path.relative_to(root).as_posix()
                try:
                    entry = self._parse_map(path, source_path=rel)
                    if (
                        entry.key in self.excluded_keys
                        or entry.key in self.firebase_inactive_keys
                    ):
                        continue
                    if entry.key in raw_catalog and not is_override:
                        issues.append(
                            f"duplicate canonical resource {entry.key}: {entry.source_path}"
                        )
                        continue
                    raw_catalog[entry.key] = entry
                    source_to_raw_key[entry.source_path] = entry.key
                except Exception as exc:
                    issues.append(f"{rel}: {exc}")
        if not raw_catalog:
            raise RuntimeError("repository contains no usable racing maps")

        reserved_keys = set(raw_catalog)
        catalog: dict[str, MapEntry] = {}
        resolved_keys: dict[str, str] = {}
        for raw_key in sorted(raw_catalog):
            raw_entry = raw_catalog[raw_key]
            entry = self._resolve_immutable_entry(
                raw_entry,
                reserved_keys,
                issues,
            )
            if entry.key in catalog:
                raise RuntimeError(
                    f"resolved map key collision at {entry.key}"
                )
            catalog[entry.key] = entry
            resolved_keys[raw_key] = entry.key
            reserved_keys.add(entry.key)

        source_to_key = {
            source: resolved_keys[raw_key]
            for source, raw_key in source_to_raw_key.items()
            if raw_key in resolved_keys
        }
        self.catalog = catalog
        self.source_to_key = source_to_key
        self.issues = issues
        self._build_public_mirror()
        try:
            self._write_parsed_catalog_cache()
        except OSError:
            LOG.exception("unable to persist parsed Firebase catalog cache")
        LOG.info(
            "loaded %d maps from repository (%d issue(s))",
            len(catalog),
            len(issues),
        )
        for issue in issues[:20]:
            LOG.warning("map repository issue: %s", issue)

    def _stored_paths(self, key: str) -> tuple[Path, ...]:
        return tuple(
            root / key
            for root in (self.public_dir, self.cache_dir, self.revision_dir)
        )

    def _entry_conflicts_with_stored_bytes(self, entry: MapEntry) -> bool:
        source_bytes = entry.local_path.read_bytes()
        return any(
            path.is_file() and path.read_bytes() != source_bytes
            for path in self._stored_paths(entry.key)
        )

    def _matching_revision(
        self,
        entry: MapEntry,
        reserved_keys: set[str],
    ) -> MapEntry | None:
        parent = self.revision_dir.joinpath(*entry.key.split("/")[:-1])
        if not parent.is_dir():
            return None
        source_bytes = entry.local_path.read_bytes()
        for path in sorted(parent.iterdir()):
            if not path.is_file() or not path.name.endswith(MAP_SUFFIX):
                continue
            try:
                candidate = self._parse_map(path, source_path=entry.source_path)
            except Exception:
                continue
            if candidate.key in reserved_keys:
                continue
            if (
                candidate.author.casefold() != entry.author.casefold()
                or candidate.category.casefold() != entry.category.casefold()
                or candidate.name.casefold() != entry.name.casefold()
            ):
                continue
            if (
                rewrite_map_resource_version(source_bytes, candidate.version)
                == path.read_bytes()
            ):
                return candidate
        return None

    def _key_exists(self, key: str, reserved_keys: set[str]) -> bool:
        if key in reserved_keys:
            return True
        return any(
            (root / key).exists()
            for root in (
                self.public_dir,
                self.cache_dir,
                self.override_dir,
                self.revision_dir,
            )
        )

    def _resolve_immutable_entry(
        self,
        entry: MapEntry,
        reserved_keys: set[str],
        issues: list[str],
    ) -> MapEntry:
        if not self._entry_conflicts_with_stored_bytes(entry):
            return entry

        if self.firebase is not None:
            raise FirebaseCatalogError(
                f"Firebase reused immutable resource path {entry.key} with different bytes"
            )

        existing = self._matching_revision(entry, reserved_keys)
        if existing is not None:
            issues.append(
                f"same-version content change for {entry.key}; "
                f"reusing immutable revision {existing.key}"
            )
            return existing

        version = bump_resource_version(entry.version)
        category_parts = [part for part in entry.category.split("/") if part]
        while True:
            key = "/".join(
                [
                    entry.author,
                    *category_parts,
                    f"{entry.name}-{version}{MAP_SUFFIX}",
                ]
            )
            if not self._key_exists(key, reserved_keys):
                break
            version = bump_resource_version(version)

        destination = self.revision_dir / key
        destination.parent.mkdir(parents=True, exist_ok=True)
        data = rewrite_map_resource_version(entry.local_path.read_bytes(), version)
        temporary = destination.with_name(
            f".{destination.name}.{os.getpid()}.tmp"
        )
        try:
            with temporary.open("xb") as handle:
                handle.write(data)
                handle.flush()
                os.fsync(handle.fileno())
            os.chmod(temporary, 0o644)
            os.replace(temporary, destination)
        finally:
            with contextlib.suppress(FileNotFoundError):
                temporary.unlink()

        resolved = self._parse_map(destination, source_path=entry.source_path)
        issues.append(
            f"same-version content change for {entry.key}; "
            f"published repository bytes as {resolved.key}"
        )
        return resolved

    def create_size_revision(self, entry: MapEntry, size_factor: float) -> MapEntry:
        """Create a persistent versioned override with a map-local SIZE_FACTOR."""
        document = ET.parse(entry.local_path)
        root = document.getroot()
        resource = root if local_name(root.tag) == "Resource" else next(
            node for node in root.iter() if local_name(node.tag) == "Resource"
        )
        map_node = next(node for node in resource.iter() if local_name(node.tag) == "Map")

        version = bump_resource_version(entry.version)
        while True:
            key = "/".join(
                [
                    entry.author,
                    *([part for part in entry.category.split("/") if part]),
                    f"{entry.name}-{version}{MAP_SUFFIX}",
                ]
            )
            destination = self.override_dir / key
            if key not in self.catalog and not destination.exists():
                break
            version = bump_resource_version(version)

        resource.set("version", version)
        settings = next(
            (child for child in map_node if local_name(child.tag) == "Settings"),
            None,
        )
        namespace = map_node.tag.split("}", 1)[0] + "}" if "}" in map_node.tag else ""
        if settings is None:
            settings = ET.Element(namespace + "Settings")
            settings.text = "\n"
            settings.tail = map_node.text or "\n"
            map_node.insert(0, settings)
        size_settings = [
            child
            for child in settings
            if local_name(child.tag) == "Setting"
            and child.attrib.get("name", "").casefold() == "size_factor"
        ]
        if not size_settings:
            setting = ET.Element(namespace + "Setting")
            setting.set("name", "SIZE_FACTOR")
            setting.tail = settings.text or "\n"
            settings.append(setting)
            size_settings.append(setting)
        for setting in size_settings:
            setting.set("value", format_size_factor(size_factor))

        destination.parent.mkdir(parents=True, exist_ok=True)
        temporary = destination.with_name(destination.name + ".tmp")
        raw = entry.local_path.read_bytes()
        encoding_match = re.search(br"<\?xml[^>]*encoding=[\"']([^\"']+)", raw[:512])
        encoding = encoding_match.group(1).decode("ascii") if encoding_match else "utf-8"
        doctype_match = re.search(br"<!DOCTYPE[^>]+>", raw[:4096], re.IGNORECASE)
        document.write(temporary, encoding=encoding, xml_declaration=True)
        if doctype_match:
            serialized = temporary.read_bytes()
            declaration_end = serialized.find(b"?>")
            insert_at = declaration_end + 2 if declaration_end >= 0 else 0
            serialized = (
                serialized[:insert_at]
                + b"\n"
                + doctype_match.group(0)
                + serialized[insert_at:]
            )
            temporary.write_bytes(serialized)
        os.replace(temporary, destination)
        revision = self._parse_map(destination, source_path=key)
        if self.firebase is not None:
            if not entry.map_id or not entry.revision_id:
                raise FirebaseCatalogError(
                    "active map is missing Firebase map/revision identity"
                )
            assert self.firebase is not None
            published = self.firebase.publish_size_revision(
                map_id=entry.map_id,
                expected_revision_id=entry.revision_id,
                data=destination.read_bytes(),
                identity={
                    "authorName": revision.author,
                    "category": revision.category,
                    "mapName": revision.name,
                    "mapVersion": revision.version,
                },
                size_factor=size_factor,
            )
            # The catalog manifest builder runs asynchronously after the
            # Firestore commit. Loading the full maps collection immediately
            # used hundreds of document reads and let the leader advance before
            # a follower could possibly obtain the same revision. Poll only
            # the single invalidation document, then consume the first compact
            # manifest that contains the published immutable resource.
            deadline = time.monotonic() + self.firebase_publish_wait_seconds
            seen_signatures: set[tuple[int, str, str]] = set()
            while True:
                state = self.firebase.get_catalog_state()
                signature = (
                    int(state.get("catalogVersion") or 0),
                    str(state.get("generation") or ""),
                    str(state.get("serverManifestSha256") or ""),
                )
                if all(signature) and signature not in seen_signatures:
                    seen_signatures.add(signature)
                    if (
                        signature[0] != self.firebase_catalog_version
                        or signature[1] != self.firebase_generation
                    ):
                        self.sync(catalog_state=state)
                        selected = self.catalog.get(revision.key)
                        if (
                            selected is not None
                            and selected.revision_id == published["revisionId"]
                        ):
                            return selected
                if time.monotonic() >= deadline:
                    raise FirebaseCatalogError(
                        f"published size revision {revision.key} did not reach "
                        "the server catalog before the timeout"
                    )
                time.sleep(1.0)
        return revision

    def set_map_status(self, key: str, status: str, reason: str) -> None:
        """Publish active/inactive status when Firebase is authoritative."""
        if self.firebase is None:
            return
        metadata = self.firebase_maps_by_key.get(key)
        if not metadata or not metadata.get("mapId"):
            raise FirebaseCatalogError(f"map {key} has no Firebase catalog identity")
        self.firebase.set_map_status(str(metadata["mapId"]), status, reason)
        self.sync(force_firestore=True)

    def list_map_reviews(self) -> list[dict]:
        if self.firebase is None:
            return []
        return self.firebase.list_map_reviews()

    def submit_map_review(self, key: str, reason: str) -> dict:
        if self.firebase is None:
            raise FirebaseCatalogError("map review requires the Firebase catalog")
        metadata = self.firebase_maps_by_key.get(key)
        if not metadata or not metadata.get("mapId"):
            raise FirebaseCatalogError(f"map {key} has no Firebase catalog identity")
        review = self.firebase.submit_map_review(str(metadata["mapId"]), reason)
        self.sync(force_firestore=True)
        return review

    def cancel_map_review(self, review_id: str, reason: str) -> dict:
        if self.firebase is None:
            raise FirebaseCatalogError("map review requires the Firebase catalog")
        review = self.firebase.cancel_map_review(review_id, reason)
        self.sync(force_firestore=True)
        return review

    @staticmethod
    def map_size_factor(entry: MapEntry) -> float | None:
        document = ET.parse(entry.local_path)
        result = None
        for node in document.getroot().iter():
            if (
                local_name(node.tag) == "Setting"
                and node.attrib.get("name", "").casefold() == "size_factor"
            ):
                result = float(node.attrib["value"])
        return result

    def _cached_ghost_map_geometry(
        self,
        path: Path,
        size_factor: float,
    ) -> tuple | None:
        try:
            stat = path.stat()
            key = (
                str(path.resolve()),
                stat.st_mtime_ns,
                stat.st_size,
                float(size_factor),
            )
        except (OSError, TypeError, ValueError):
            return None
        cache = self._ghost_geometry_cache
        if key not in cache:
            if len(cache) >= 1024:
                cache.clear()
            cache[key] = ghost_map_geometry(path, size_factor)
        return cache[key]

    def ghost_coordinate_scale(
        self,
        current: MapEntry,
        recorded_resource_key: str,
        recorded_size_factor: float | None,
        current_size_factor: float | None,
    ) -> float | None:
        """Return the safe start-coordinate conversion for a historical map."""
        public_root = self.public_dir.resolve()
        try:
            recorded_path = (public_root / recorded_resource_key).resolve()
        except (OSError, RuntimeError):
            return None
        if (
            public_root != recorded_path
            and public_root not in recorded_path.parents
        ):
            return None
        if not recorded_path.is_file():
            return None

        try:
            active_factor = float(
                current_size_factor
                if current_size_factor is not None
                else (self.map_size_factor(current) or 0.0)
            )
        except (OSError, ET.ParseError, TypeError, ValueError):
            return None
        if not math.isfinite(active_factor) or abs(active_factor) > 100:
            return None
        active_geometry = self._cached_ghost_map_geometry(
            current.local_path,
            active_factor,
        )
        if active_geometry is None:
            return None

        candidate_factors: list[float] = []
        if recorded_size_factor is not None:
            try:
                candidate_factors.append(float(recorded_size_factor))
            except (TypeError, ValueError):
                pass
        try:
            recorded_entry = self._parse_map(
                recorded_path,
                source_path=recorded_resource_key,
            )
            embedded_factor = self.map_size_factor(recorded_entry)
            candidate_factors.append(
                float(embedded_factor) if embedded_factor is not None else 0.0
            )
        except (
            ET.ParseError,
            KeyError,
            OSError,
            StopIteration,
            TypeError,
            ValueError,
        ):
            return None

        tried: set[float] = set()
        for candidate_factor in candidate_factors:
            if (
                candidate_factor in tried
                or not math.isfinite(candidate_factor)
                or abs(candidate_factor) > 100
            ):
                continue
            tried.add(candidate_factor)
            if (
                self._cached_ghost_map_geometry(recorded_path, candidate_factor)
                == active_geometry
            ):
                return 2.0 ** ((candidate_factor - active_factor) / 2.0)
        return None

    def _build_public_mirror(self) -> None:
        self.public_dir.mkdir(parents=True, exist_ok=True)
        for entry in self.catalog.values():
            destination = self.public_dir / entry.key
            install_immutable_file(entry.local_path, destination)
        if self.dtd_source_dir.is_dir():
            for dtd in self.dtd_source_dir.rglob("*.dtd"):
                destination = self.public_dir / dtd.name
                if not destination.exists():
                    shutil.copy2(dtd, destination)
        # sty.dtd is commonly supplied by the resource repository rather than
        # installed with the game data. Preserve any copy the game has already
        # cached and expose it from the mirror root for clients.
        for dtd in self.cache_dir.glob("*.dtd"):
            destination = self.public_dir / dtd.name
            if not destination.exists() or destination.stat().st_mtime_ns != dtd.stat().st_mtime_ns:
                shutil.copy2(dtd, destination)

    def cache_for_server(self, entry: MapEntry) -> None:
        destination = self.cache_dir / entry.key
        install_immutable_file(entry.local_path, destination)
        for dtd in self.public_dir.glob("*.dtd"):
            cached_dtd = self.cache_dir / dtd.name
            if not cached_dtd.exists():
                shutil.copy2(dtd, cached_dtd)



    def find_by_spec(self, spec: str) -> MapEntry | None:
        key = spec.split("(", 1)[0]
        if key in self.catalog:
            return self.catalog[key]
        cached = self.cache_dir / key
        if cached.is_file():
            try:
                return self._parse_external(cached, key)
            except Exception as exc:
                LOG.warning("unable to parse active external map %s: %s", key, exc)
        published = self.public_dir / key
        if published.is_file():
            try:
                return self._parse_external(published, key)
            except Exception as exc:
                LOG.warning("unable to parse published map %s: %s", key, exc)
        source_key = self.source_to_key.get(key)
        if source_key:
            return self.catalog[source_key]
        return None

    def _parse_external(self, path: Path, key: str) -> MapEntry:
        entry = self._parse_map(path, source_path=key)
        return dataclasses.replace(entry, key=key, source_path=key, local_path=path)

    def display_name(self, entry: MapEntry) -> str:
        """Return a deterministic selector for maps that share a name."""
        siblings = sorted(
            (
                candidate
                for candidate in self.catalog.values()
                if candidate.name.casefold() == entry.name.casefold()
            ),
            key=lambda candidate: (
                candidate.author.casefold(),
                candidate.version.casefold(),
                candidate.key.casefold(),
            ),
        )
        if len(siblings) < 2:
            return entry.name
        for number, candidate in enumerate(siblings, 1):
            if candidate.key == entry.key:
                return f"{entry.name} {number}"
        return entry.name

    def search(self, query: str) -> list[MapEntry]:
        query_fold = query.strip().casefold()
        normalized = normalized_map_name(query)
        exact: list[MapEntry] = []
        partial: list[MapEntry] = []
        for entry in self.catalog.values():
            names = {
                entry.name.casefold(),
                self.display_name(entry).casefold(),
                entry.key.casefold(),
                Path(entry.key).name[: -len(MAP_SUFFIX)].casefold(),
            }
            normalized_names = {normalized_map_name(item) for item in names}
            if query_fold in names or (normalized and normalized in normalized_names):
                exact.append(entry)
            elif query_fold and any(query_fold in item for item in names):
                partial.append(entry)
            elif normalized and any(normalized in item for item in normalized_names):
                partial.append(entry)
        return sorted(
            exact or partial,
            key=lambda item: (
                self.display_name(item).casefold(),
                item.author.casefold(),
                item.key.casefold(),
            ),
        )


class QuietStaticHandler(http.server.SimpleHTTPRequestHandler):
    def log_message(self, fmt: str, *args) -> None:
        LOG.debug("map mirror: " + fmt, *args)

    def list_directory(self, path):
        self.send_error(404, "Directory listing disabled")
        return None

    def end_headers(self) -> None:
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Cache-Control", "public, max-age=300")
        super().end_headers()


class MirrorServer:
    def __init__(self, root: Path, bind: str, port: int):
        handler = functools.partial(QuietStaticHandler, directory=str(root))
        self.server = http.server.ThreadingHTTPServer((bind, port), handler)
        self.thread = threading.Thread(target=self.server.serve_forever, name="map-mirror", daemon=True)

    def start(self) -> None:
        self.thread.start()

    def close(self) -> None:
        self.server.shutdown()
        self.server.server_close()
        self.thread.join(timeout=5)




class TronnerRacing:
    def __init__(self, config: dict):
        self.config = config
        self.started_at_epoch = time.time()
        self.hot_commands = HotCommandRegistry(
            Path(
                config.get(
                    "hot_commands_dir",
                    Path(__file__).resolve().with_name("hot_commands"),
                )
            )
        )
        configured_encoding = config.get("game_text_encoding", "auto")
        fallback_encoding = config.get(
            "game_text_encoding_fallback",
            DEFAULT_GAME_TEXT_ENCODING,
        )
        self.game_text_encoding_auto = (
            str(configured_encoding).strip().casefold() == "auto"
        )
        if self.game_text_encoding_auto:
            self.game_text_encoding = detect_game_text_encoding(
                Path(config.get("ladderlog", "")),
                fallback_encoding,
            )
        else:
            self.game_text_encoding = canonical_game_text_encoding(
                configured_encoding,
                fallback_encoding,
            )
        self.sink = CommandSink(
            Path(config["console_input"]),
            self.game_text_encoding,
        )
        self.repository = MapRepository(config)
        self.store = StateStore(Path(config["database"]))
        saved_start_preferences = self.store.get_json(
            START_PREFERENCES_STORAGE_KEY, None
        )
        migrate_legacy_start_preferences = not isinstance(
            saved_start_preferences, dict
        )
        if migrate_legacy_start_preferences:
            saved_start_preferences = self.store.get_json("start_preferences", {})
        self.start_preferences: dict[str, str] = {}
        for identity_key, raw_preference in (
            saved_start_preferences.items()
            if isinstance(saved_start_preferences, dict)
            else ()
        ):
            preference = normalize_start_preference(raw_preference)
            if migrate_legacy_start_preferences and preference is not None:
                # The old optional countdown number had a different meaning.
                # Preserve the mode, but default the new respawn delay to zero.
                preference = preference.split()[0]
            if preference is not None:
                self.start_preferences[str(identity_key)] = preference
        if migrate_legacy_start_preferences:
            self.store.set_json(
                START_PREFERENCES_STORAGE_KEY, self.start_preferences
            )
        saved_result_preferences = self.store.get_json(
            "result_message_preferences", {}
        )
        self.result_message_preferences: dict[str, bool] = {
            str(identity_key): enabled
            for identity_key, enabled in (
                saved_result_preferences.items()
                if isinstance(saved_result_preferences, dict)
                else ()
            )
            if isinstance(enabled, bool)
        }
        saved_ghost_preferences = self.store.get_json("ghost_preferences", {})
        self.ghost_preferences: dict[str, str] = {}
        for identity_key, raw_preference in (
            saved_ghost_preferences.items()
            if isinstance(saved_ghost_preferences, dict)
            else ()
        ):
            preference = normalize_ghost_preference(raw_preference)
            if preference is not None:
                self.ghost_preferences[str(identity_key)] = preference
        # Migrate the persistent selectors saved by the old map-scoped format.
        legacy_ghost_selections = self.store.get_json("ghost_selections", {})
        legacy_items = (
            legacy_ghost_selections.get("selections", {}).items()
            if isinstance(legacy_ghost_selections, dict)
            and isinstance(legacy_ghost_selections.get("selections"), dict)
            else ()
        )
        for identity_key, raw_state in legacy_items:
            if not isinstance(raw_state, dict):
                continue
            preference = normalize_ghost_preference(raw_state.get("selector"))
            if preference is not None:
                self.ghost_preferences.setdefault(str(identity_key), preference)
        self.store.set_json("ghost_preferences", self.ghost_preferences)
        self.store.set_json("ghost_selections", {})
        self.ghost_selections: dict[str, dict[str, object]] = {}
        self.ghost_selection_map_key = ""
        self.spawn_preferences_path = Path(
            config.get(
                "spawn_preferences_file",
                "/var/lib/tronner-racing/spawn_preferences.json",
            )
        )
        loaded_preferences = load_json_object(self.spawn_preferences_path).get(
            "preferences", {}
        )
        self.spawn_preferences: dict[str, dict[str, int]] = (
            loaded_preferences if isinstance(loaded_preferences, dict) else {}
        )
        self.command_windows: dict[int, collections.deque[float]] = {}
        self.command_warning_times: dict[int, float] = {}
        saved_helpful_cycle = self.store.get_json("helpful_message_cycle", {})
        self.helpful_message_cycle: dict = (
            saved_helpful_cycle if isinstance(saved_helpful_cycle, dict) else {}
        )
        saved_helpful_round_token = self.store.get_json(
            "helpful_message_round_token", None
        )
        self.helpful_message_round_token: str | None = (
            str(saved_helpful_round_token) if saved_helpful_round_token else None
        )
        self.helpful_message_round_generation = 0
        self.helpful_message_announced = False
        self._helpful_message_task: asyncio.Task | None = None
        self._server_options_last: str | None = None
        self.report_last_sent: dict[str, float] = {}
        saved_report_epochs = self.store.get_json("report_success_epochs", [])
        self.report_success_epochs: collections.deque[float] = collections.deque()
        if isinstance(saved_report_epochs, list):
            for value in saved_report_epochs:
                with contextlib.suppress(TypeError, ValueError):
                    self.report_success_epochs.append(float(value))
        self.excluded_map_keys: set[str] = set(
            self.store.get_json("excluded_map_keys", [])
        )
        loaded_exclusion_reasons = self.store.get_json(
            "excluded_map_reasons", {}
        )
        self.excluded_map_reasons: dict[str, str] = (
            {
                str(key): str(reason)
                for key, reason in loaded_exclusion_reasons.items()
                if str(key) in self.excluded_map_keys and str(reason).strip()
            }
            if isinstance(loaded_exclusion_reasons, dict)
            else {}
        )
        self.repository.excluded_keys = self.excluded_map_keys
        self.catalog_state_signature: tuple[int, str, str] | None = None
        self.catalog_ack_signature: tuple[int, str, str] | None = None
        self.next_activity_probe_monotonic = 0.0
        self.players: dict[str, Player] = {}
        self.aliases: dict[str, Player] = {}
        self.rotation: collections.deque[str] = collections.deque(
            self.store.get_json("rotation", [])
        )
        self.queue: collections.deque[str] = collections.deque(
            self.store.get_json("queue", [])
        )
        saved_queue_attribution = self.store.get_json("queue_attribution", {})
        self.queue_attribution: dict[str, dict[str, object]] = (
            {
                str(key): dict(value)
                for key, value in saved_queue_attribution.items()
                if isinstance(value, dict)
            }
            if isinstance(saved_queue_attribution, dict)
            else {}
        )
        saved_pending_size_change = self.store.get_json(
            "pending_size_change", {}
        )
        self.pending_size_change: dict[str, str] = (
            {
                key: str(saved_pending_size_change.get(key, ""))
                for key in (
                    "source_map_key",
                    "target_map_key",
                    "source_records_key",
                    "target_records_key",
                )
            }
            if isinstance(saved_pending_size_change, dict)
            and saved_pending_size_change.get("target_map_key")
            else {}
        )
        self.cycle_played: set[str] = set(self.store.get_json("cycle_played", []))
        # Upgrade state written by versions that only persisted the remaining
        # rotation.  The active repository map has necessarily been consumed.
        if not self.cycle_played:
            saved_current = self.store.get_json("current_key", None)
            if saved_current:
                self.cycle_played.add(saved_current)
        self.current: MapEntry | None = None
        self.current_spec: str | None = None
        self.current_size_factor: float | None = None
        saved_previous_map = self.store.get_json("previous_map_metadata", {})
        self.previous_map_metadata: dict[str, object] = (
            saved_previous_map if isinstance(saved_previous_map, dict) else {}
        )
        saved_map_history = self.store.get_json("map_history", [])
        self.map_history: collections.deque[dict[str, object]] = collections.deque(
            (
                dict(item)
                for item in saved_map_history
                if isinstance(item, dict) and item.get("mapKey")
            ),
            maxlen=MAP_HISTORY_LIMIT,
        ) if isinstance(saved_map_history, list) else collections.deque(
            maxlen=MAP_HISTORY_LIMIT
        )
        saved_current_selection = self.store.get_json(
            "current_map_selection", {}
        )
        self.current_map_selection: dict[str, object] = (
            dict(saved_current_selection)
            if isinstance(saved_current_selection, dict)
            else {}
        )
        self.next_map_selection: dict[str, object] = {}
        self.restoring_saved_map = False
        self.deadline_epoch: float | None = self.store.get_json("deadline_epoch", None)
        self.round_started_epoch: float | None = self.store.get_json(
            "round_started_epoch", None
        )
        self.extend_votes: set[str] = set()
        self.skip_votes: set[str] = set()
        self.extend_vote_generation = 0
        self.skip_vote_generation = 0
        self.round_active = False
        self.round_started_map_key: str | None = self.store.get_json(
            "round_started_map_key", None
        )
        self.transitioning = bool(self.store.get_json("transitioning", False))
        self.transition_target_key: str | None = self.store.get_json(
            "transition_target_key", None
        )
        if self.transitioning and not self.transition_target_key:
            self.transition_target_key = self.store.get_json("current_key", None)
        self.transition_map_confirmed = False
        self.transition_observed_key: str | None = None
        self.transition_started_epoch: float | None = None
        self.transition_round_started_pending = False
        self.final_countdown_active = bool(
            self.store.get_json("final_countdown_active", False)
        )
        self.final_countdown_end_epoch: float | None = self.store.get_json(
            "final_countdown_end_epoch", None
        )
        self.final_countdown_map_key: str | None = self.store.get_json(
            "final_countdown_map_key", None
        )
        self.final_countdown_announcement: str | None = None
        self.finalists: set[int] = set()
        self.finishes_in_progress: set[int] = set()
        self.final_countdown_route_model: RouteModel | None = None
        self.final_countdown_route_map_key: str | None = None
        self.final_countdown_route_building = False
        self.final_countdown_route_prepared = False
        self.final_countdown_route_tasks: set[asyncio.Task] = set()
        self.final_countdown_progress_states: dict[int, PlayerProgressState] = {}
        self.final_countdown_duration_seconds: float | None = None
        self.final_countdown_acceleration_capability: AccelerationCapability | None
        self.final_countdown_acceleration_capability = None
        self.final_countdown_acceleration_identifier: str | None = None
        reload_state = self.store.get_json("controller_reload", {})
        self.controller_reload_state: dict = (
            reload_state if isinstance(reload_state, dict) else {}
        )
        self.respawns_paused = bool(self.controller_reload_state.get("pending"))
        self.controller_reload_draining = False
        self._controller_reload_task: asyncio.Task | None = None
        self.server_restart_active = False
        self._server_restart_task: asyncio.Task | None = None
        self.last_game_time: float | None = None
        self.last_game_monotonic: float | None = None
        self.respawn_tasks: dict[int, asyncio.Task] = {}
        self.freeze_tasks: dict[int, asyncio.Task] = {}
        self.center_clear_tasks: dict[int, asyncio.Task] = {}
        self.replay_captures: dict[str, ReplayCapture] = {}
        self.active_replay_tokens: dict[int, str] = {}
        self.replay_settings_assemblies: dict[str, ReplaySettingsAssembly] = {}
        self.active_replay_settings_identifier: str | None = None
        # online_players.txt is rewritten in place by the game server.  A read
        # can therefore briefly omit a player who is actually connected.  Do
        # not let one incomplete snapshot override authoritative ladderlog
        # lifecycle events.
        self.online_snapshot_misses: dict[int, int] = {}
        self.last_time_left_minute: int | None = None
        self.map_lock = asyncio.Lock()
        self.stop_event = asyncio.Event()
        self.mirror: MirrorServer | None = None
        self._display_task: asyncio.Task | None = None
        self._transition_watchdog_task: asyncio.Task | None = None
        self.server_id = clean_console_text(
            config.get("server_id", config.get("firebase_server_id", "local"))
        )
        if not re.fullmatch(
            r"[A-Za-z0-9][A-Za-z0-9._:-]{0,63}", self.server_id
        ):
            raise ValueError("invalid server_id")
        live_config = config.get("live_dashboard", {})
        if not isinstance(live_config, dict):
            live_config = {}
        self.server_console_path = Path(
            live_config.get(
                "console_log_path",
                "/var/lib/armagetronad/consolelog.txt",
            )
        )
        self.server_console_entries: collections.deque[dict[str, object]] = (
            collections.deque(maxlen=SERVER_CONSOLE_HISTORY_LINES)
        )
        self.server_console_sequence = 0
        self.server_console_last_published_sequence = 0
        self.server_console_stream_until_monotonic = 0.0
        self.server_console_available = False
        self._live_dashboard_tasks: set[asyncio.Task] = set()
        self.live_dashboard: FirebaseLiveDashboardPublisher | None = None
        self.live_dashboard_chat: FirebaseLiveDashboardPublisher | None = None
        self.live_dashboard_refresh_requested = False
        if (
            isinstance(live_config, dict)
            and live_config.get("enabled") is True
            and self.live_dashboard_authority
            and self.repository.firebase is not None
        ):
            self.live_dashboard = FirebaseLiveDashboardPublisher(
                self.repository.firebase,
                str(live_config.get("database_url", "")),
                self.store,
            )
            self.live_dashboard_chat = self.live_dashboard
        elif (
            isinstance(live_config, dict)
            and live_config.get("chat_enabled") is True
            and self.repository.firebase is not None
        ):
            self.live_dashboard_chat = FirebaseLiveDashboardPublisher(
                self.repository.firebase,
                str(live_config.get("database_url", "")),
                self.store,
            )



    @property
    def live_dashboard_authority(self) -> bool:
        return True

    def _round_is_active(self) -> bool:
        return bool(getattr(self, "round_active", False))

    def _apply_advertised_game_encoding(self, advertised: object) -> None:
        current = getattr(
            self,
            "game_text_encoding",
            canonical_game_text_encoding(DEFAULT_GAME_TEXT_ENCODING),
        )
        encoding = canonical_game_text_encoding(advertised, current)
        if not getattr(self, "game_text_encoding_auto", True):
            if encoding != current:
                LOG.warning(
                    "Armagetron advertised %s but server-script encoding is locked to %s",
                    encoding,
                    current,
                )
            return
        if encoding != current:
            LOG.info(
                "Armagetron text encoding changed from %s to %s",
                current,
                encoding,
            )
        self.game_text_encoding = encoding
        sink = getattr(self, "sink", None)
        if hasattr(sink, "set_encoding"):
            sink.set_encoding(encoding)

    def _decode_game_bytes(self, data: bytes, context: str) -> str:
        encoding = getattr(
            self,
            "game_text_encoding",
            canonical_game_text_encoding(DEFAULT_GAME_TEXT_ENCODING),
        )
        return decode_game_text(data, encoding, context)

    async def initialize(self, start_http: bool = True) -> None:
        LOG.info("using Armagetron text encoding %s", self.game_text_encoding)
        if self.repository.firebase is not None:
            local_manifest = self.repository.checkout / ".catalog.json"
            use_local_snapshot = (
                local_manifest.is_file()
                and (
                    not self.config.get("repository_auto_sync", True)
                    or bool(self.controller_reload_state.get("pending"))
                )
            )
            if use_local_snapshot:
                await asyncio.to_thread(self.repository.load_local_snapshot)
            else:
                await asyncio.to_thread(self.repository.sync)
            # The background invalidation watcher owns Firebase reconciliation.
            # Seeding its signature prevents it from downloading and scanning the
            # same immutable generation immediately after a fast local startup.
            self.catalog_state_signature = self.repository.local_catalog_signature()
        elif (
            self.config.get("repository_auto_sync", True)
            or not (self.repository.checkout / ".git").is_dir()
        ):
            await asyncio.to_thread(self.repository.sync)
        else:
            await asyncio.to_thread(self.repository.scan)
        replay_migration = await asyncio.to_thread(
            self.store.rekey_replay_maps,
            self._replay_record_key_aliases(),
            self.server_id,
        )
        if replay_migration.map_rows:
            LOG.info(
                "normalized %d replay map reference(s) covering %d run(s), "
                "%d finished; marked %d record(s) available and rewound "
                "replay publication cursor from %d to %d",
                replay_migration.map_rows,
                replay_migration.replay_runs,
                replay_migration.finished_runs,
                replay_migration.records_marked,
                replay_migration.previous_cursor,
                replay_migration.replay_cursor,
            )
        self._migrate_spawn_preferences()
        self._reconcile_rotation()
        self._restore_runtime_context()
        await self._restore_persistent_ghosts_for_round()
        if self.transitioning:
            self._schedule_transition_watchdog(self.transition_target_key)
        if start_http:
            self.mirror = MirrorServer(
                self.repository.public_dir,
                self.config.get("public_bind", "0.0.0.0"),
                int(self.config.get("public_port", 8080)),
            )
            self.mirror.start()
        # CURRENT_MAP is emitted during grid creation before ROUND_STARTED.
        # Keeping the writer enabled makes transition confirmation ordered and
        # removes a timing race during controller reload recovery.
        initialization_commands = [
            "LADDERLOG_WRITE_CURRENT_MAP 1",
            "GET_CURRENT_MAP",
        ]
        await self.sink.send(*initialization_commands)
        await self._resume_controller_reload()

    async def reconcile_map_reviews_once(self) -> None:
        """Reconcile legacy local exclusions after startup is already usable."""
        if self.repository.firebase is None or not self.excluded_map_keys:
            return
        try:
            reviews = await asyncio.to_thread(self.repository.list_map_reviews)
            review_keys = {
                str(item.get("sourceResourcePath") or "") for item in reviews
            }
            catalog_keys = set(self.repository.firebase_maps_by_key)
            retained_exclusions = {
                key
                for key in self.excluded_map_keys
                if key in catalog_keys and key not in review_keys
            }
            if retained_exclusions == self.excluded_map_keys:
                return
            removed = self.excluded_map_keys - retained_exclusions
            async with self.map_lock:
                self.excluded_map_keys = retained_exclusions
                self.repository.excluded_keys = retained_exclusions
                self.store.set_json(
                    "excluded_map_keys", sorted(self.excluded_map_keys)
                )
                self.excluded_map_reasons = {
                    key: reason
                    for key, reason in self.excluded_map_reasons.items()
                    if key in self.excluded_map_keys
                }
                self.store.set_json(
                    "excluded_map_reasons", self.excluded_map_reasons
                )
                await asyncio.to_thread(self.repository.load_local_snapshot)
                self._reconcile_rotation()
            LOG.info(
                "removed %d stale/reviewed key(s) from permanent exclusions",
                len(removed),
            )
        except asyncio.CancelledError:
            raise
        except Exception:
            LOG.exception("background map-review reconciliation failed")

    def _save_ghost_preferences(self) -> None:
        self.store.set_json(
            "ghost_preferences", getattr(self, "ghost_preferences", {})
        )

    def _clear_ghost_selections(self) -> None:
        """Clear resolved plans for a map while retaining player preferences."""
        self.ghost_selections = {}
        self.ghost_selection_map_key = ""

    def _move_ghost_selection(self, old_identity: str, new_identity: str) -> None:
        selections = getattr(self, "ghost_selections", {})
        if old_identity == new_identity:
            return
        if old_identity in selections:
            state = selections.pop(old_identity)
            selections.setdefault(new_identity, state)
        preferences = getattr(self, "ghost_preferences", {})
        if old_identity in preferences:
            preference = preferences.pop(old_identity)
            preferences.setdefault(new_identity, preference)
            self._save_ghost_preferences()

    async def _restore_persistent_ghosts_for_round(self) -> None:
        if (
            not getattr(self, "current", None)
            or not getattr(self, "round_active", False)
            or getattr(self, "transitioning", False)
        ):
            return
        seen_players: set[int] = set()
        for player in list(getattr(self, "players", {}).values()):
            if id(player) in seen_players or not player.connected or player.is_ai:
                continue
            seen_players.add(id(player))
            selector = getattr(self, "ghost_preferences", {}).get(
                player.identity_key
            )
            if selector:
                await self._command_ghost(
                    player, selector, automatic=True, silent=True
                )

    def _restore_runtime_context(self) -> None:
        """Recover non-record state when the controller restarts mid-round."""
        online_path = Path(self.config.get("online_players_file", ""))
        try:
            online_lines = self._decode_game_bytes(
                online_path.read_bytes(),
                "online player snapshot",
            ).splitlines()
            first_line = online_lines[0]
            entry = self.repository.find_by_spec(first_line)
            if entry:
                self.current = entry
                self.current_spec = first_line
                if self._pending_size_target_key() == entry.key:
                    self._consume_pending_size_change(entry)
                if (
                    self.transitioning
                    and self.transition_target_key == entry.key
                ):
                    self.transition_map_confirmed = True
            self._bootstrap_players_from_lines(online_lines[1:], authoritative=True)
        except (OSError, IndexError):
            pass

        if (
            self.final_countdown_active
            and self.current
            and self.final_countdown_map_key != self.current.key
        ):
            self._clear_final_countdown_state()

        ladder_path = Path(self.config.get("ladderlog", ""))
        try:
            with ladder_path.open("rb") as handle:
                size = handle.seek(0, os.SEEK_END)
                start = max(0, size - 1024 * 1024)
                handle.seek(start)
                if start:
                    # A byte-size tail can begin inside a protocol line or a
                    # multibyte character; only reconstruct complete events.
                    handle.readline()
                data = self._decode_game_bytes(
                    handle.read(),
                    "ladderlog recovery tail",
                )
        except OSError:
            return
        round_state: bool | None = None
        latest_game_time: float | None = None
        for line in data.splitlines():
            event, _, payload = line.partition(" ")
            if event == "ROUND_STARTED":
                round_state = True
            elif event in {
                "NEW_ROUND",
                "ROUND_FINISHED",
                "ROUND_ENDED",
                "SHUTDOWN",
            }:
                round_state = False
            elif event == "GAME_TIME":
                with contextlib.suppress(ValueError, IndexError):
                    latest_game_time = float(payload.split()[-1])
            elif event == "PLAYER_ENTERED_GRID":
                self._handle_player_entered(payload, True, clear_center=False)
            elif event == "PLAYER_LEAVES_SPECTATORS":
                self._handle_player_entered(payload, True, clear_center=False)
            elif event == "PLAYER_ENTERED_SPECTATOR":
                self._handle_player_entered(
                    payload, False, clear_center=False
                )
            elif event == "PLAYER_JOINS_SPECTATORS":
                self._handle_player_entered(payload, False, clear_center=False)
            elif event == "PLAYER_LEFT":
                self._handle_player_left(payload)
            elif event == "PLAYER_LOGIN":
                self._handle_player_login(payload)
            elif event == "PLAYER_LOGOUT":
                self._handle_player_logout(payload)
            elif event == "PLAYER_RENAMED":
                self._handle_player_renamed(payload)
            elif event == "PLAYER_COLORED_NAME":
                self._handle_player_colored_name(payload)
            elif event == "PLAYER_AI_ENTERED":
                self._handle_player_ai_entered(payload)
            elif event == "ONLINE_PLAYER":
                self._handle_online_player(payload)
            elif event == "ONLINE_PLAYERS_ALIVE":
                self._handle_online_status(payload, True)
            elif event == "ONLINE_PLAYERS_DEAD":
                self._handle_online_status(payload, False)
        if round_state is not None:
            self.round_active = round_state
        if self.round_active and self.current:
            self._set_round_started_map(self.current.key)
        if (
            self.transitioning
            and self.transition_map_confirmed
            and self.round_active
        ):
            # The controller may restart after CURRENT_MAP and ROUND_STARTED
            # were already emitted. The live map plus the reconstructed round
            # state are enough to acknowledge that completed transition.
            LOG.info(
                "completing restored map transition: %s",
                self.transition_target_key,
            )
            self._complete_map_transition()
        if latest_game_time is not None:
            self.last_game_time = latest_game_time
            self.last_game_monotonic = time.monotonic()

    def close(self) -> None:
        for task in self.respawn_tasks.values():
            task.cancel()
        for task in self.freeze_tasks.values():
            task.cancel()
        for task in self.center_clear_tasks.values():
            task.cancel()
        if self._display_task:
            self._display_task.cancel()
        if self._transition_watchdog_task:
            self._transition_watchdog_task.cancel()
        if self._helpful_message_task:
            self._helpful_message_task.cancel()
        if self._controller_reload_task:
            self._controller_reload_task.cancel()
        if self._server_restart_task:
            self._server_restart_task.cancel()
        for task in self._live_dashboard_tasks:
            task.cancel()
        self._live_dashboard_tasks.clear()
        if self.mirror:
            self.mirror.close()
        for capture in list(self.replay_captures.values()):
            if capture.outcome == "death":
                capture.outcome = "controller_stop"
            self._persist_replay_capture(capture)
        self.replay_captures.clear()
        self.active_replay_tokens.clear()
        self.store.close()

    def request_controller_reload(self, requested_by: str = "system") -> bool:
        if self._controller_reload_task and not self._controller_reload_task.done():
            return False
        self._controller_reload_task = asyncio.create_task(
            self._drain_for_controller_reload(requested_by),
            name="controller-reload-drain",
        )
        return True

    def request_server_restart(self, requested_by: str = "system") -> float | None:
        if (
            self.server_restart_active
            or self.transitioning
            or self.final_countdown_active
            or self.controller_reload_draining
            or self.controller_reload_state.get("pending")
            or not self.current
        ):
            return None
        records = self.store.records(map_records_key(self.current))
        duration = final_countdown_seconds(records)
        self.server_restart_active = True
        self.respawns_paused = True
        self._server_restart_task = asyncio.create_task(
            self._run_server_restart_countdown(duration, requested_by),
            name="server-restart-countdown",
        )
        return duration

    async def _run_server_restart_countdown(
        self,
        duration: float,
        requested_by: str,
    ) -> None:
        try:
            await self._disable_practice_for_countdown()
            self._clear_all_votes()
            for task in self.respawn_tasks.values():
                task.cancel()
            self.respawn_tasks.clear()
            held_players: list[Player] = []
            for player in {
                id(item): item for item in self.players.values()
            }.values():
                if player.pending_respawn:
                    held_players.append(player)
                    self._cancel_player_freeze(player)
            if held_players:
                await self.sink.send(
                    *(f"KILL_SILENT {player.target}" for player in held_players)
                )

            total_seconds = max(1, math.ceil(duration))
            await self.sink.send(
                "CONSOLE_MESSAGE 0xff0000SERVER RESTARTING IN "
                f"{total_seconds} SECONDS"
            )
            LOG.info(
                "server restart countdown requested_by=%s duration=%.3f",
                clean_console_text(requested_by),
                duration,
            )
            end_monotonic = time.monotonic() + duration
            last_number: int | None = None
            while self.server_restart_active:
                remaining = end_monotonic - time.monotonic()
                if remaining <= 0:
                    await self.sink.send(server_restart_center_command(0))
                    break
                number = max(1, math.ceil(remaining))
                if number != last_number:
                    await self.sink.send(server_restart_center_command(number))
                    last_number = number
                await asyncio.sleep(0.05)

            # Accept the same map's first ROUND_STARTED after systemd brings
            # the processes back. Persisted map state lets the new controller
            # restore the current map without treating it as a native repeat.
            self._set_round_started_map(None)
            self.round_active = False
            self.server_restart_active = False
            await self.sink.send("QUIT")
            await asyncio.sleep(0.1)
            self.stop_event.set()
        except asyncio.CancelledError:
            raise
        finally:
            if self._server_restart_task is asyncio.current_task():
                self._server_restart_task = None

    def _controller_reload_alive_players(self) -> list[Player]:
        unique: dict[int, Player] = {}
        for player in self.players.values():
            if (
                player.connected
                and player.active
                and player.alive
                and not player.is_ai
            ):
                unique[id(player)] = player
        return list(unique.values())

    async def _drain_for_controller_reload(self, requested_by: str) -> None:
        self.respawns_paused = True
        self.controller_reload_draining = True
        now = time.time()
        resume_identity_keys = sorted(
            {
                player.identity_key
                for player in self.players.values()
                if player.connected
                and player.active
                and player.respawn_enabled
                and not player.is_ai
            }
        )
        deadline_remaining = (
            max(0.0, self.deadline_epoch - now)
            if self.deadline_epoch is not None
            else None
        )
        final_countdown_remaining = (
            max(0.0, self.final_countdown_end_epoch - now)
            if self.final_countdown_active
            and self.final_countdown_end_epoch is not None
            else None
        )
        self.controller_reload_state = {
            "version": 1,
            "pending": True,
            "map_key": self.current.key if self.current else None,
            "requested_at": now,
            "requested_by": clean_console_text(requested_by),
            "deadline_remaining": deadline_remaining,
            "final_countdown_remaining": final_countdown_remaining,
            "resume_identity_keys": resume_identity_keys,
        }
        self.store.set_json("controller_reload", self.controller_reload_state)

        for task in self.respawn_tasks.values():
            task.cancel()
        self.respawn_tasks.clear()
        held_players: list[Player] = []
        for player in {id(item): item for item in self.players.values()}.values():
            if player.pending_respawn:
                held_players.append(player)
                self._cancel_player_freeze(player)
        if held_players:
            await self.sink.send(
                *(f"KILL_SILENT {player.target}" for player in held_players)
            )

        alive = self._controller_reload_alive_players()
        if alive:
            await self.broadcast(
                "Server script reload pending. Respawns are paused; "
                f"waiting for {len(alive)} active "
                f"{'run' if len(alive) == 1 else 'runs'} to finish.",
            )
        while self._controller_reload_alive_players() or self.finishes_in_progress:
            await asyncio.sleep(0.05)

        await self.broadcast(
            "Active runs are complete. Reloading the server script; "
            "respawns will resume shortly.",
        )
        await asyncio.sleep(0.1)
        self.stop_event.set()

    async def _resume_controller_reload(self) -> None:
        state = self.controller_reload_state
        if not state.get("pending"):
            self.respawns_paused = False
            recovered = self._schedule_startup_respawns()
            if recovered:
                LOG.info(
                    "scheduled %d dead racer(s) after server-script startup",
                    recovered,
                )
            return
        same_map = bool(
            self.current
            and state.get("map_key")
            and self.current.key == state.get("map_key")
        )
        resume_grace = max(
            1.0,
            float(self.config.get("controller_reload_resume_grace_seconds", 5)),
        )
        now = time.time()
        if same_map and state.get("deadline_remaining") is not None:
            self.deadline_epoch = now + max(
                resume_grace, float(state["deadline_remaining"])
            )
            self.store.set_json("deadline_epoch", self.deadline_epoch)
        if (
            same_map
            and self.final_countdown_active
            and state.get("final_countdown_remaining") is not None
        ):
            self.final_countdown_end_epoch = now + max(
                resume_grace, float(state["final_countdown_remaining"])
            )
            self.store.set_json(
                "final_countdown_end_epoch", self.final_countdown_end_epoch
            )

        resume_identity_keys = set(state.get("resume_identity_keys", []))
        self.controller_reload_state = {}
        self.store.set_json("controller_reload", {})
        self.respawns_paused = False
        self.controller_reload_draining = False
        recovered = 0
        if same_map:
            recovered = self._schedule_startup_respawns(resume_identity_keys)
        if recovered:
            LOG.info(
                "scheduled %d dead racer(s) after graceful server-script reload",
                recovered,
            )
        await self.broadcast(
            "Server script reload complete. Respawning resumed.",
        )

    def _schedule_startup_respawns(
        self,
        identity_keys: set[str] | None = None,
    ) -> int:
        """Recover eligible dead racers after any mid-round controller start."""
        if (
            not self.current
            or not self.round_active
            or self.transitioning
            or self.final_countdown_active
            or getattr(self, "respawns_paused", False)
        ):
            return 0
        scheduled = 0
        for player in {id(item): item for item in self.players.values()}.values():
            if (
                identity_keys is not None
                and player.identity_key not in identity_keys
            ):
                continue
            if (
                player.connected
                and player.active
                and player.respawn_enabled
                and not player.alive
                and not player.pending_respawn
                and not player.is_ai
                and id(player) not in self.respawn_tasks
            ):
                self._schedule_respawn(player, delay_seconds=0.1)
                scheduled += 1
        return scheduled























    def _save_spawn_preferences(self) -> None:
        atomic_write_json(
            self.spawn_preferences_path,
            {"version": 2, "preferences": self.spawn_preferences},
        )

    def _migrate_spawn_preferences(self) -> None:
        """Replace revision-specific resource keys with stable map identities."""
        if not self.spawn_preferences:
            return
        active_by_rating_key = {
            entry.rating_key: entry
            for entry in self.repository.catalog.values()
        }
        migrated: dict[str, dict[str, int]] = {}
        unresolved: dict[str, dict[str, int]] = {}

        # Preserve already-migrated values first so a stale legacy alias cannot
        # overwrite a newer preference written by this controller version.
        for key, preferences in self.spawn_preferences.items():
            if key.startswith(("map-id:", "logical:", "resource:")) and isinstance(
                preferences, dict
            ):
                migrated[key] = dict(preferences)

        for key, preferences in self.spawn_preferences.items():
            if key.startswith(("map-id:", "logical:", "resource:")):
                continue
            if not isinstance(preferences, dict):
                continue
            entry = self.repository.find_by_spec(key)
            if entry is None:
                unresolved[key] = dict(preferences)
                continue
            active_entry = active_by_rating_key.get(entry.rating_key, entry)
            destination = migrated.setdefault(
                map_spawn_preferences_key(active_entry), {}
            )
            for identity_key, number in preferences.items():
                destination.setdefault(identity_key, number)

        updated = {**unresolved, **migrated}
        if updated != self.spawn_preferences:
            self.spawn_preferences = updated
            self._save_spawn_preferences()
            LOG.info(
                "migrated spawn preferences to stable map identities "
                "(%d map(s), %d unresolved legacy key(s))",
                len(migrated),
                len(unresolved),
            )

    def _spawn_preferences_for(
        self,
        entry: MapEntry,
        create: bool = False,
    ) -> dict[str, int]:
        """Return preferences for a map and absorb any remaining legacy aliases."""
        stable_key = map_spawn_preferences_key(entry)
        preferences = self.spawn_preferences.get(stable_key)
        aliases = (entry.key, f"logical:{entry.rating_key}")
        changed = False
        for alias in aliases:
            if alias == stable_key:
                continue
            legacy = self.spawn_preferences.pop(alias, None)
            if not isinstance(legacy, dict):
                continue
            if preferences is None:
                preferences = {}
            for identity_key, number in legacy.items():
                preferences.setdefault(identity_key, number)
            changed = True
        if preferences is None and create:
            preferences = {}
            changed = True
        if preferences is not None:
            self.spawn_preferences[stable_key] = preferences
        if changed:
            self._save_spawn_preferences()
        return preferences if preferences is not None else {}

    def _save_start_preferences(self) -> None:
        self.store.set_json(
            START_PREFERENCES_STORAGE_KEY, self.start_preferences
        )





    def _start_mode_for(self, player: Player) -> str:
        mode = str(getattr(player, "start_mode", "immediate")).casefold()
        fallback_delay = float(
            getattr(
                player,
                "start_respawn_delay_seconds",
                DEFAULT_START_RESPAWN_DELAY_SECONDS,
            )
        )
        fallback_value = (
            mode if fallback_delay == 0 else f"{mode} {fallback_delay:g}"
        )
        _, _, fallback = start_preference_details(fallback_value)
        preferences = getattr(self, "start_preferences", {})
        saved_mode, saved_delay, _ = start_preference_details(
            preferences.get(player.identity_key, fallback)
        )
        player.start_mode = saved_mode
        player.start_respawn_delay_seconds = saved_delay
        return saved_mode

    def _preferred_spawn_index(self, player: Player) -> int | None:
        if not self.current or not self.current.spawns:
            return None
        map_preferences = self._spawn_preferences_for(self.current)
        try:
            number = int(map_preferences.get(player.identity_key, 0))
        except (TypeError, ValueError):
            return None
        if 1 <= number <= len(self.current.spawns):
            return number - 1
        return None

    async def _command_rate_allowed(self, player: Player) -> bool:
        now = time.monotonic()
        window_seconds = max(
            1.0, float(self.config.get("command_rate_window_seconds", 5.0))
        )
        maximum = max(1, int(self.config.get("command_rate_maximum", 4)))
        player_key = id(player)
        window = self.command_windows.setdefault(player_key, collections.deque())
        while window and now - window[0] >= window_seconds:
            window.popleft()
        if len(window) < maximum:
            window.append(now)
            return True
        warning_interval = max(
            1.0,
            float(
                self.config.get(
                    "command_rate_warning_interval_seconds", window_seconds
                )
            ),
        )
        last_warning = self.command_warning_times.get(player_key, -math.inf)
        if now - last_warning >= warning_interval:
            self.command_warning_times[player_key] = now
            await self.private(player, "Command rate limit reached. Please wait.")
        return False

    def _save_rotation(self) -> None:
        queued_keys = set(self.queue)
        self.queue_attribution = {
            key: value
            for key, value in getattr(self, "queue_attribution", {}).items()
            if key in queued_keys and isinstance(value, dict)
        }
        self.store.set_json("rotation", list(self.rotation))
        self.store.set_json("queue", list(self.queue))
        self.store.set_json("queue_attribution", self.queue_attribution)
        self.store.set_json("cycle_played", sorted(self.cycle_played))

    def _attribute_queued_map(
        self,
        key: str,
        queued_by: str,
        queued_via: str,
    ) -> None:
        if not hasattr(self, "queue_attribution"):
            self.queue_attribution = {}
        self.queue_attribution[key] = {
            "queued": True,
            "queuedBy": plain_console_text(queued_by).strip()[:128] or "Unknown",
            "queuedVia": clean_console_text(queued_via)[:32] or "server",
            "queuedAt": int(time.time() * 1000),
        }

    def _selection_for_map(
        self,
        entry: MapEntry,
        *,
        queued: bool = False,
        queued_by: str = "",
        queued_via: str = "rotation",
        queued_at: int | None = None,
    ) -> dict[str, object]:
        return {
            "resourcePath": entry.key,
            "queued": bool(queued),
            "queuedBy": plain_console_text(queued_by).strip()[:128],
            "queuedVia": clean_console_text(queued_via)[:32] or "rotation",
            "queuedAt": max(0, int(queued_at or 0)),
        }

    def _set_current_map_selection(self, entry: MapEntry) -> None:
        selection = dict(getattr(self, "next_map_selection", {}))
        if selection.get("resourcePath") != entry.key:
            selection = self._selection_for_map(entry, queued_via="native")
        selection["selectedAt"] = int(time.time() * 1000)
        self.current_map_selection = selection
        self.next_map_selection = {}
        self.store.set_json("current_map_selection", selection)

    def _dashboard_upcoming_rotation(
        self,
        limit: int = UPCOMING_ROTATION_LIMIT,
    ) -> list[dict[str, object]]:
        maximum = max(1, min(int(limit), UPCOMING_ROTATION_LIMIT))
        # Refill at the same boundary used by _peek_next so the preview and the
        # map the controller will actually take cannot disagree.
        self._peek_next()
        upcoming: list[dict[str, object]] = []
        current_key = self.current.key if self.current else None
        pending_size_key = self._pending_size_target_key()
        if pending_size_key and pending_size_key != current_key:
            pending_entry = self.repository.catalog.get(pending_size_key)
            if pending_entry:
                attribution = getattr(self, "queue_attribution", {}).get(
                    pending_size_key, {}
                )
                upcoming.append({
                    **self._dashboard_map_metadata(pending_entry),
                    **self._selection_for_map(
                        pending_entry,
                        queued=bool(attribution),
                        queued_by=str(attribution.get("queuedBy", "")),
                        queued_via=str(
                            attribution.get("queuedVia", "scheduled resize")
                        ),
                        queued_at=int(attribution.get("queuedAt", 0) or 0),
                    ),
                })
        for key in self.queue:
            if len(upcoming) >= maximum or key == current_key:
                continue
            entry = self.repository.catalog.get(key)
            if not entry:
                continue
            attribution = getattr(self, "queue_attribution", {}).get(key, {})
            upcoming.append({
                **self._dashboard_map_metadata(entry),
                **self._selection_for_map(
                    entry,
                    queued=True,
                    queued_by=str(attribution.get("queuedBy", "Unknown")),
                    queued_via=str(attribution.get("queuedVia", "server")),
                    queued_at=int(attribution.get("queuedAt", 0) or 0),
                ),
            })
        queued_keys = set(self.queue)
        for key in self.rotation:
            if len(upcoming) >= maximum:
                break
            if key == current_key or key in queued_keys or key == pending_size_key:
                continue
            entry = self.repository.catalog.get(key)
            if entry:
                upcoming.append({
                    **self._dashboard_map_metadata(entry),
                    **self._selection_for_map(entry),
                })
        return upcoming[:maximum]

    def _pending_size_target_key(self) -> str | None:
        pending = getattr(self, "pending_size_change", {})
        if not isinstance(pending, dict):
            return None
        target = str(pending.get("target_map_key", "")).strip()
        return target or None

    def _clear_pending_size_change(self) -> None:
        self.pending_size_change = {}
        self.store.set_json("pending_size_change", {})

    def _consume_pending_size_change(
        self,
        entry: MapEntry,
    ) -> tuple[int, int] | None:
        """Reset superseded records once the scheduled resized map activates."""
        if self._pending_size_target_key() != entry.key:
            return None
        pending = self.pending_size_change
        record_keys = []
        for field in ("source_records_key", "target_records_key"):
            key = str(pending.get(field, "")).strip()
            if key and key not in record_keys:
                record_keys.append(key)
        reset_records = 0
        reset_finishes = 0
        for key in record_keys:
            record_count, finish_count = self.store.reset_map(key)
            reset_records += record_count
            reset_finishes += finish_count
        self._clear_pending_size_change()
        LOG.info(
            "activated resized map %s; reset %d records and %d finishes",
            entry.key,
            reset_records,
            reset_finishes,
        )
        return reset_records, reset_finishes

    def _display_map_name(self, entry: MapEntry) -> str:
        repository = getattr(self, "repository", None)
        if repository is not None and hasattr(repository, "display_name"):
            return repository.display_name(entry)
        return entry.name

    @staticmethod
    def _excluded_key_parts(key: str) -> tuple[str, str, str]:
        """Return a readable name, author, and version from a resource key."""
        parts = key.split("/")
        author = parts[0] if len(parts) > 1 else "Unknown"
        filename = parts[-1]
        stem = (
            filename[: -len(MAP_SUFFIX)]
            if filename.endswith(MAP_SUFFIX)
            else filename
        )
        if "-" in stem:
            name, version = stem.rsplit("-", 1)
        else:
            name, version = stem, "?"
        return name or filename, author or "Unknown", version

    def _excluded_map_rows(self) -> list[tuple[str, str, str, str, str]]:
        """Return key/name/author/version/selector rows for excluded maps."""
        parsed = [
            (key, *self._excluded_key_parts(key))
            for key in self.excluded_map_keys
        ]
        parsed.sort(
            key=lambda row: (
                row[1].casefold(),
                row[2].casefold(),
                row[3].casefold(),
                row[0].casefold(),
            )
        )
        totals = collections.Counter(row[1].casefold() for row in parsed)
        positions: collections.Counter[str] = collections.Counter()
        rows = []
        for key, name, author, version in parsed:
            positions[name.casefold()] += 1
            selector = (
                f"{name} {positions[name.casefold()]}"
                if totals[name.casefold()] > 1
                else name
            )
            rows.append((key, name, author, version, selector))
        return rows

    def _search_excluded_maps(
        self,
        query: str,
    ) -> list[tuple[str, str, str, str, str]]:
        query_fold = query.strip().casefold()
        normalized = normalized_map_name(query)
        exact = []
        partial = []
        for row in self._excluded_map_rows():
            key, name, author, version, selector = row
            names = {
                key.casefold(),
                name.casefold(),
                selector.casefold(),
                f"{name} by {author}".casefold(),
                f"{selector} by {author}".casefold(),
                Path(key).name[: -len(MAP_SUFFIX)].casefold(),
            }
            normalized_names = {normalized_map_name(item) for item in names}
            if query_fold in names or (normalized and normalized in normalized_names):
                exact.append(row)
            elif query_fold and any(query_fold in item for item in names):
                partial.append(row)
            elif normalized and any(normalized in item for item in normalized_names):
                partial.append(row)
        return exact or partial

    @staticmethod
    def _review_map_rows(
        reviews: Sequence[dict],
    ) -> list[tuple[str, str, str, str, str, str, str]]:
        """Return review-id/key/name/author/version/status/selector rows."""
        parsed = [
            (
                str(review.get("_id") or review.get("submissionId") or ""),
                str(review.get("sourceResourcePath") or ""),
                str(review.get("mapName") or "Untitled"),
                str(review.get("authorName") or "Unknown"),
                str(review.get("mapVersion") or "?"),
                str(review.get("status") or "pending"),
            )
            for review in reviews
        ]
        parsed = [row for row in parsed if row[0]]
        parsed.sort(
            key=lambda row: (
                row[2].casefold(),
                row[3].casefold(),
                row[4].casefold(),
                row[0].casefold(),
            )
        )
        totals = collections.Counter(row[2].casefold() for row in parsed)
        positions: collections.Counter[str] = collections.Counter()
        rows = []
        for review_id, key, name, author, version, status in parsed:
            positions[name.casefold()] += 1
            selector = (
                f"{name} {positions[name.casefold()]}"
                if totals[name.casefold()] > 1
                else name
            )
            rows.append(
                (review_id, key, name, author, version, status, selector)
            )
        return rows

    def _search_map_reviews(
        self,
        reviews: Sequence[dict],
        query: str,
    ) -> list[tuple[str, str, str, str, str, str, str]]:
        query_fold = query.strip().casefold()
        normalized = normalized_map_name(query)
        exact = []
        partial = []
        for row in self._review_map_rows(reviews):
            review_id, key, name, author, version, _, selector = row
            names = {
                review_id.casefold(),
                key.casefold(),
                name.casefold(),
                selector.casefold(),
                f"{name} by {author}".casefold(),
                f"{selector} by {author}".casefold(),
            }
            normalized_names = {normalized_map_name(item) for item in names}
            if query_fold in names or (normalized and normalized in normalized_names):
                exact.append(row)
            elif query_fold and any(query_fold in item for item in names):
                partial.append(row)
            elif normalized and any(normalized in item for item in normalized_names):
                partial.append(row)
        return exact or partial

    async def _exclude_map_key(self, key: str, reason: str = "") -> None:
        """Persistently remove one canonical resource from every map selector."""
        self.excluded_map_keys.add(key)
        if not hasattr(self, "excluded_map_reasons"):
            self.excluded_map_reasons = {}
        if reason.strip():
            self.excluded_map_reasons[key] = reason.strip()
        self.repository.excluded_keys = self.excluded_map_keys
        self.store.set_json("excluded_map_keys", sorted(self.excluded_map_keys))
        self.store.set_json("excluded_map_reasons", self.excluded_map_reasons)
        self.repository.catalog.pop(key, None)
        source_to_key = getattr(self.repository, "source_to_key", {})
        for source, mapped_key in list(source_to_key.items()):
            if mapped_key == key:
                source_to_key.pop(source, None)
        self.rotation = collections.deque(item for item in self.rotation if item != key)
        self.queue = collections.deque(item for item in self.queue if item != key)
        self.cycle_played.discard(key)
        self._save_rotation()

    def _reconcile_rotation(self) -> None:
        available = set(self.repository.catalog)
        self.cycle_played.intersection_update(available)
        seen: set[str] = set()
        retained = []
        for key in self.rotation:
            if key in available and key not in self.cycle_played and key not in seen:
                retained.append(key)
                seen.add(key)
        # A repository refresh may add maps, but must never re-add maps already
        # consumed in this shuffle cycle.
        additions = list(available - seen - self.cycle_played)
        random.SystemRandom().shuffle(additions)
        retained.extend(additions)
        self.rotation = collections.deque(retained)
        self.queue = collections.deque(key for key in self.queue if key in available)
        self._save_rotation()

    def _refill_rotation(self) -> None:
        current_key = self.current.key if self.current else None
        keys = [
            key for key in self.repository.catalog
            if key != current_key
        ]
        random.SystemRandom().shuffle(keys)
        self.cycle_played.clear()
        self.rotation = collections.deque(keys)

    def _peek_next(self) -> MapEntry | None:
        current_key = self.current.key if self.current else None
        pending_size_key = self._pending_size_target_key()
        if pending_size_key and pending_size_key != current_key:
            pending_entry = self.repository.catalog.get(pending_size_key)
            if pending_entry is not None:
                return pending_entry
        for key in self.queue:
            if key != current_key:
                return self.repository.catalog.get(key)
        if not self.rotation:
            self._refill_rotation()
        for key in self.rotation:
            if key != current_key:
                return self.repository.catalog.get(key)
        return None

    def _server_options_text(self) -> str:
        current = self.current
        current_name = self._display_map_name(current) if current else "Unknown"
        current_author = current.author if current else "Unknown"
        next_entry = self._peek_next()
        next_name = self._display_map_name(next_entry) if next_entry else "Unknown"
        next_author = next_entry.author if next_entry else "Unknown"
        return clean_console_text(
            f"Current map: {current_name} by {current_author} | "
            f"Next Map: {next_name} by {next_author}"
        )

    async def _refresh_server_options_once(self) -> None:
        options = self._server_options_text()
        if options != self._server_options_last:
            await self.sink.send(
                f"SERVER_OPTIONS {readline_console_text(options)}"
            )
            self._server_options_last = options

    async def server_options_refresher(self) -> None:
        interval = max(
            0.25,
            float(self.config.get("server_options_refresh_seconds", 1.0)),
        )
        while not self.stop_event.is_set():
            try:
                await self._refresh_server_options_once()
            except Exception:
                LOG.exception("server options refresh failed")
            await asyncio.sleep(interval)

    def _take_next(self) -> MapEntry | None:
        current_key = self.current.key if self.current else None
        key = None
        selection: dict[str, object] = {}
        pending_size_key = self._pending_size_target_key()
        if pending_size_key and pending_size_key != current_key:
            if pending_size_key in self.repository.catalog:
                key = pending_size_key
                attribution = getattr(self, "queue_attribution", {}).get(
                    pending_size_key, {}
                )
                selection = self._selection_for_map(
                    self.repository.catalog[pending_size_key],
                    queued=bool(attribution),
                    queued_by=str(attribution.get("queuedBy", "")),
                    queued_via=str(
                        attribution.get("queuedVia", "scheduled resize")
                    ),
                    queued_at=int(attribution.get("queuedAt", 0) or 0),
                )
                self.queue = collections.deque(
                    item for item in self.queue if item != pending_size_key
                )
                self.rotation = collections.deque(
                    item for item in self.rotation if item != pending_size_key
                )
            else:
                LOG.error(
                    "scheduled resized map is unavailable; clearing target: %s",
                    pending_size_key,
                )
                self._clear_pending_size_change()
        while self.queue and key is None:
            candidate = self.queue.popleft()
            if candidate == current_key:
                LOG.warning("discarding current map from next-map queue: %s", candidate)
                continue
            key = candidate
            entry = self.repository.catalog.get(key)
            attribution = getattr(self, "queue_attribution", {}).get(key, {})
            if entry:
                selection = self._selection_for_map(
                    entry,
                    queued=True,
                    queued_by=str(attribution.get("queuedBy", "Unknown")),
                    queued_via=str(attribution.get("queuedVia", "server")),
                    queued_at=int(attribution.get("queuedAt", 0) or 0),
                )
            with contextlib.suppress(ValueError):
                self.rotation.remove(key)
        if key is None:
            if not self.rotation:
                self._refill_rotation()
            while self.rotation and key is None:
                candidate = self.rotation.popleft()
                if candidate == current_key:
                    LOG.warning("discarding current map from rotation head: %s", candidate)
                    continue
                key = candidate
                entry = self.repository.catalog.get(key)
                if entry:
                    selection = self._selection_for_map(entry)
        if key is None:
            # A restored rotation can contain only the active map at the end
            # of a shuffle cycle. Refill once after discarding it so another
            # available map is still selected.
            self._refill_rotation()
            if self.rotation:
                key = self.rotation.popleft()
                entry = self.repository.catalog.get(key)
                if entry:
                    selection = self._selection_for_map(entry)
        if key:
            self.cycle_played.add(key)
        self.next_map_selection = selection
        self._save_rotation()
        return self.repository.catalog.get(key) if key else None

    def _set_round_started_map(self, key: str | None) -> None:
        self.round_started_map_key = key
        self.store.set_json("round_started_map_key", key)

    def _begin_map_transition(self, target_key: str) -> None:
        """Wait for the target map before accepting its ROUND_STARTED event."""
        self._set_round_started_map(None)
        self.transitioning = True
        self.transition_target_key = target_key
        self.transition_map_confirmed = False
        self.transition_observed_key = None
        self.transition_started_epoch = time.time()
        self.transition_round_started_pending = False
        self.store.set_json("transitioning", True)
        self.store.set_json("transition_target_key", target_key)
        self._schedule_transition_watchdog(target_key)

    def _complete_map_transition(self) -> None:
        self.transitioning = False
        self.transition_target_key = None
        self.transition_map_confirmed = False
        self.transition_observed_key = None
        self.transition_started_epoch = None
        self.transition_round_started_pending = False
        self.store.set_json("transitioning", False)
        self.store.set_json("transition_target_key", None)
        task = getattr(self, "_transition_watchdog_task", None)
        self._transition_watchdog_task = None
        if task:
            with contextlib.suppress(RuntimeError):
                if task is not asyncio.current_task():
                    task.cancel()

    def _schedule_transition_watchdog(self, target_key: str | None) -> None:
        if not target_key:
            return
        old_task = getattr(self, "_transition_watchdog_task", None)
        if old_task and not old_task.done():
            old_task.cancel()
        self._transition_watchdog_task = asyncio.create_task(
            self._watch_map_transition(target_key),
            name=f"map-transition-{target_key}",
        )

    async def _watch_map_transition(self, target_key: str) -> None:
        """Recover when Armagetron rejects a requested map and falls back."""
        timeout = max(
            0.05,
            float(self.config.get("map_transition_timeout_seconds", 20.0)),
        )
        probe_delay = max(
            0.05,
            float(self.config.get("map_transition_probe_seconds", 1.0)),
        )
        confirmations_required = max(
            1,
            int(self.config.get("map_transition_failure_confirmations", 2)),
        )
        mismatch_count = 0
        try:
            await asyncio.sleep(timeout)
            while (
                self.transitioning
                and self.transition_target_key == target_key
                and not self.transition_map_confirmed
            ):
                # CURRENT_MAP is authoritative. Requiring repeated fresh replies
                # prevents a slow but valid map change from being mistaken for a
                # load failure merely because an old ROUND_STARTED was queued.
                self.transition_observed_key = None
                await self.sink.send("GET_CURRENT_MAP")
                await asyncio.sleep(probe_delay)
                if (
                    not self.transitioning
                    or self.transition_target_key != target_key
                    or self.transition_map_confirmed
                ):
                    return
                observed_key = self.transition_observed_key
                if observed_key and observed_key != target_key:
                    mismatch_count += 1
                    LOG.warning(
                        "map transition probe %d/%d: requested=%s active=%s",
                        mismatch_count,
                        confirmations_required,
                        target_key,
                        observed_key,
                    )
                    if mismatch_count >= confirmations_required:
                        await self._recover_failed_map_transition(
                            target_key,
                            observed_key,
                        )
                        return
                else:
                    mismatch_count = 0
                await asyncio.sleep(probe_delay)
        except asyncio.CancelledError:
            raise
        except Exception:
            LOG.exception("map transition watchdog failed for %s", target_key)
        finally:
            if (
                getattr(self, "_transition_watchdog_task", None)
                is asyncio.current_task()
            ):
                self._transition_watchdog_task = None

    async def _recover_failed_map_transition(
        self,
        target_key: str,
        active_key: str,
    ) -> None:
        if not self.transitioning or self.transition_target_key != target_key:
            return
        failed_entry = self.repository.catalog.get(target_key)
        failed_name = (
            self._display_map_name(failed_entry)
            if failed_entry
            else self._excluded_key_parts(target_key)[0]
        )
        failed_author = (
            failed_entry.author
            if failed_entry
            else self._excluded_key_parts(target_key)[1]
        )
        try:
            await asyncio.to_thread(
                publish_repository_map_status,
                self.repository,
                target_key,
                "inactive",
                "Server automatically deactivated a map that failed to load",
            )
        except Exception:
            # Transition recovery must not wait indefinitely on an external
            # catalog. The durable local exclusion remains authoritative for
            # this server until a later admin/retry reconciles Firebase.
            LOG.exception("unable to publish failed-map exclusion to Firebase")
        await self._exclude_map_key(
            target_key,
            "Server automatically deactivated a map that failed to load",
        )
        LOG.error(
            "map failed to load; excluded requested=%s active=%s",
            target_key,
            active_key,
        )
        self._complete_map_transition()
        try:
            await self.broadcast(
                f"ERROR: Failed to load {failed_name} by {failed_author}. "
                "It was added to the exclusion list; advancing to the next map."
            )
        finally:
            await self.activate_next_map("previous map failed to load")

    def _effective_map_size_factor(self, entry: MapEntry) -> float:
        default = float(self.config.get("default_size_factor", 0))
        try:
            embedded = self.repository.map_size_factor(entry)
        except (OSError, ET.ParseError, TypeError, ValueError):
            LOG.exception("unable to read embedded SIZE_FACTOR for %s", entry.key)
            return default
        if embedded is None:
            return default
        value = float(embedded)
        if not math.isfinite(value) or abs(value) > 1000:
            LOG.warning("ignoring invalid embedded SIZE_FACTOR for %s", entry.key)
            return default
        return value

    async def activate_next_map(self, reason: str) -> None:
        if getattr(self, "controller_reload_draining", False):
            LOG.info(
                "deferring map advance during server-script reload drain: %s",
                reason,
            )
            return
        async with self.map_lock:
            previous_key = self.current.key if self.current else ""
            entry = self._take_next()
            if not entry:
                LOG.error("cannot advance map: repository catalog is empty")
                return
            await asyncio.to_thread(self.repository.cache_for_server, entry)
            # Announce the value the map will actually apply when its grid is
            # built so dashboard state matches the activated revision.
            size_factor = self._effective_map_size_factor(entry)
            LOG.info("advancing to %s (%s)", entry.key, reason)
            size_reset = self._consume_pending_size_change(entry)
            self._clear_final_countdown_state()
            self._remember_previous_map(self.current)
            self.current = entry
            self._clear_ghost_selections()
            self._set_current_map_selection(entry)
            self.current_spec = entry.key
            self.current_size_factor = size_factor
            self.round_started_epoch = None
            self.deadline_epoch = time.time() + self._map_open_play_seconds(entry)
            self.store.set_json("current_key", entry.key)
            self.store.set_json("deadline_epoch", self.deadline_epoch)
            self.store.set_json("round_started_epoch", None)
            self._clear_all_votes()
            self._begin_map_transition(entry.key)
            self.round_active = False
            self._cancel_helpful_message()
            self._reset_attempts()
            self._publish_dashboard_map_change(previous_key)
            # START_NEW_MATCH only schedules a reset after the current round.  Since
            # this controller respawns dead racers, that round may otherwise never
            # become empty.  transitioning is already true, so the deaths emitted
            # by KILL_ALL are deliberately not respawned.
            await self.sink.send(
                "GHOST_CLEAR_ALL",
                f"SIZE_FACTOR {format_size_factor(size_factor)}",
                f"MAP_FILE {quote_console(entry.key)}",
                "START_NEW_MATCH",
                "KILL_ALL",
                "GET_CURRENT_MAP",
            )
            announcement = (
                f"Next map: {self._display_map_name(entry)} by {entry.author}"
            )
            if size_reset is not None:
                reset_record_count, reset_finish_count = size_reset
                announcement += (
                    f". Resized revision activated; reset {reset_record_count} "
                    f"records and {reset_finish_count} finish entries"
                )
            await self.broadcast(announcement)

    def _reset_attempts(self) -> None:
        for task in self.respawn_tasks.values():
            task.cancel()
        self.respawn_tasks.clear()
        for task in self.freeze_tasks.values():
            task.cancel()
        self.freeze_tasks.clear()
        for task in self.center_clear_tasks.values():
            task.cancel()
        self.center_clear_tasks.clear()
        for player in self.players.values():
            self._clear_player_practice(player)
            player.generation += 1
            player.pending_respawn = False
            player.alive = False
            player.spawn_cursor = self._preferred_spawn_index(player) or 0
            player.last_spawn_index = None
            player.respawn_created_game = None
            player.attempt_started_game = None
            player.attempt_number = 0
            self._clear_checkpoint_run(player)

    @staticmethod
    def _clear_checkpoint_run(player: Player) -> None:
        player.checkpoints_collected.clear()
        player.checkpoint_notice_monotonic = None
        player.checkpoint_snapshot = None
        player.checkpoint_respawn_requested = False
        player.checkpoint_respawn_speed = None
        player.checkpoint_respawn_used = False
        player.pending_respawn_kind = ""
        player.no_cp_elapsed = 0.0
        player.no_cp_segment_started_game = None
        player.last_checkpoint_respawn_monotonic = None
        player.last_checkpoint_game = None

    def _map_play_seconds(self, entry: object | None = None) -> float:
        entry = entry or getattr(self, "current", None)
        minimum = max(
            120.0,
            float(self.config.get("minimum_map_duration_seconds", 120)),
        )
        maximum = max(
            minimum,
            float(self.config.get("map_duration_seconds", 300)),
        )
        if entry is None:
            return max(0.0, maximum)
        records = self.store.records(map_records_key(entry))
        return map_play_seconds(
            records,
            maximum,
            float(self.config.get("map_time_racer_multiplier", 1.25)),
            float(self.config.get("map_time_target_finishes", 5)),
            minimum,
        )

    def _map_open_play_seconds(self, entry: object | None = None) -> float:
        entry = entry or getattr(self, "current", None)
        minimum = max(
            120.0,
            float(self.config.get("minimum_map_duration_seconds", 120)),
        )
        maximum = max(
            minimum,
            float(self.config.get("map_duration_seconds", 300)),
        )
        if entry is None:
            return max(0.0, maximum)
        records = self.store.records(map_records_key(entry))
        return map_open_play_seconds(
            records,
            maximum,
            float(self.config.get("map_time_racer_multiplier", 1.25)),
            float(self.config.get("map_time_target_finishes", 5)),
            minimum,
        )

    def _begin_new_attempt(self, player: Player, event_game: float) -> None:
        self._clear_checkpoint_run(player)
        player.attempt_started_game = event_game
        player.no_cp_segment_started_game = event_game
        player.attempt_number += 1

    def _practice_active(self, player: Player) -> bool:
        current = getattr(self, "current", None)
        return bool(
            current
            and getattr(player, "practice_mode", "off") in PRACTICE_MODES
            and getattr(player, "practice_map_key", "") == current.key
        )

    @staticmethod
    def _clear_player_practice(
        player: Player,
        *,
        preserve_current_attempt: bool = False,
    ) -> None:
        player.practice_mode = "off"
        player.practice_rewind_seconds = 0.0
        player.practice_map_key = ""
        player.practice_samples.clear()
        player.practice_respawn_snapshot = None
        player.practice_start_respawn_pending = False
        player.practice_finish_pending = False
        if not preserve_current_attempt:
            player.practice_attempt_tainted = False

    async def _disable_practice_for_countdown(self) -> None:
        disabled: list[tuple[Player, bool]] = []
        for player in {
            id(item): item
            for item in getattr(self, "players", {}).values()
        }.values():
            if not self._practice_active(player):
                continue
            current_life_tainted = player.alive
            self._clear_player_practice(
                player,
                preserve_current_attempt=current_life_tainted,
            )
            disabled.append((player, current_life_tainted))
        for player, current_life_tainted in disabled:
            await self.private(
                player,
                (
                    "Practice mode was disabled for the countdown. Your current "
                    "life is still ineligible to record a time."
                    if current_life_tainted
                    else "Practice mode was disabled for the countdown."
                ),
            )

    def _record_practice_snapshot(
        self,
        player: Player,
        game_time: float,
        x: float,
        y: float,
        *,
        xdir: float | None = None,
        ydir: float | None = None,
        speed: float | None = None,
        turns: int | None = None,
    ) -> PracticeSnapshot | None:
        if not self._practice_active(player):
            return None
        values = (game_time, x, y)
        if not all(math.isfinite(value) for value in values):
            return None
        samples = player.practice_samples
        previous = samples[-1] if samples else None

        direction_length = math.hypot(xdir or 0.0, ydir or 0.0)
        if direction_length > 1e-9:
            normalized_xdir = float(xdir) / direction_length
            normalized_ydir = float(ydir) / direction_length
        else:
            direction_length = math.hypot(player.cycle_xdir, player.cycle_ydir)
            if direction_length > 1e-9:
                normalized_xdir = player.cycle_xdir / direction_length
                normalized_ydir = player.cycle_ydir / direction_length
            elif previous is not None:
                normalized_xdir = previous.xdir
                normalized_ydir = previous.ydir
            else:
                normalized_xdir, normalized_ydir = 1.0, 0.0

        resolved_speed = speed
        if resolved_speed is None or not math.isfinite(resolved_speed) or resolved_speed < 0:
            resolved_speed = player.cycle_speed
            if previous is not None:
                elapsed = game_time - previous.game_time
                if elapsed > 1e-4:
                    distance = math.hypot(x - previous.x, y - previous.y)
                    if distance > 1e-6:
                        resolved_speed = distance / elapsed
        resolved_speed = max(0.0, float(resolved_speed))
        resolved_turns = player.cycle_turns if turns is None else int(turns)
        resolved_turns = max(0, min(65535, resolved_turns))
        snapshot = PracticeSnapshot(
            game_time=float(game_time),
            x=float(x),
            y=float(y),
            xdir=normalized_xdir,
            ydir=normalized_ydir,
            speed=resolved_speed,
            turns=resolved_turns,
        )
        if previous is not None and abs(previous.game_time - game_time) <= 1e-6:
            samples[-1] = snapshot
        else:
            samples.append(snapshot)
        player.cycle_xdir = normalized_xdir
        player.cycle_ydir = normalized_ydir
        player.cycle_speed = resolved_speed
        player.cycle_turns = resolved_turns

        retention = max(
            1.0,
            float(
                self.config.get(
                    "practice_max_rewind_seconds",
                    DEFAULT_PRACTICE_MAX_REWIND_SECONDS,
                )
            ),
        ) + 2.0
        while samples and game_time - samples[0].game_time > retention:
            samples.popleft()
        return snapshot

    def _practice_rewind_target(
        self,
        player: Player,
        death_snapshot: PracticeSnapshot,
    ) -> PracticeSnapshot:
        target_time = (
            death_snapshot.game_time
            - max(0.0, float(player.practice_rewind_seconds))
        )
        return min(
            player.practice_samples or (death_snapshot,),
            key=lambda sample: abs(sample.game_time - target_time),
        )

    def _prepare_practice_respawn(
        self,
        player: Player,
        game_time: float,
        x: float,
        y: float,
        xdir: float,
        ydir: float,
        *,
        speed: float | None = None,
        turns: int | None = None,
    ) -> None:
        death_snapshot = self._record_practice_snapshot(
            player,
            game_time,
            x,
            y,
            xdir=xdir,
            ydir=ydir,
            speed=speed,
            turns=turns,
        )
        if death_snapshot is not None:
            player.practice_respawn_snapshot = self._practice_rewind_target(
                player, death_snapshot
            )

    def _observe_cycle_turn(self, player: Player, action: str) -> None:
        axes = max(1, int(getattr(self.current, "axes", 4) or 4))
        angle = (2.0 * math.pi / axes) * (1 if action == "L" else -1)
        cosine = math.cos(angle)
        sine = math.sin(angle)
        xdir, ydir = player.cycle_xdir, player.cycle_ydir
        player.cycle_xdir = xdir * cosine - ydir * sine
        player.cycle_ydir = xdir * sine + ydir * cosine
        player.cycle_turns = min(65535, player.cycle_turns + 1)

    @staticmethod
    def _resume_checkpoint_attempt(player: Player, event_game: float) -> bool:
        snapshot = player.checkpoint_snapshot
        if snapshot is None:
            return False
        player.attempt_started_game = snapshot.attempt_started_game
        player.checkpoints_collected = set(snapshot.checkpoints_collected)
        player.no_cp_elapsed = snapshot.no_cp_elapsed
        player.no_cp_segment_started_game = event_game
        player.checkpoint_respawn_used = True
        player.checkpoint_respawn_requested = False
        player.checkpoint_respawn_speed = None
        player.pending_respawn_kind = ""
        return True

    def _cancel_player_freeze(self, player: Player, clear_attempt: bool = True) -> None:
        player.generation += 1
        player.pending_respawn = False
        player.respawn_created_game = None
        player.manual_restart_pending = False
        if clear_attempt:
            player.attempt_started_game = None
            self._clear_checkpoint_run(player)
        task = self.respawn_tasks.pop(id(player), None)
        if task:
            task.cancel()
        task = self.freeze_tasks.pop(id(player), None)
        if task:
            task.cancel()
        task = self.center_clear_tasks.pop(id(player), None)
        if task:
            task.cancel()

    def _clear_final_countdown_state(self) -> None:
        self.final_countdown_active = False
        self.final_countdown_end_epoch = None
        self.final_countdown_map_key = None
        self.final_countdown_announcement = None
        self.finalists.clear()
        self.final_countdown_route_model = None
        self.final_countdown_route_map_key = None
        self.final_countdown_route_building = False
        self.final_countdown_route_prepared = False
        self.final_countdown_progress_states = {}
        self.final_countdown_duration_seconds = None
        self.final_countdown_acceleration_capability = None
        self.final_countdown_acceleration_identifier = None
        self.store.set_json("final_countdown_active", False)
        self.store.set_json("final_countdown_end_epoch", None)
        self.store.set_json("final_countdown_map_key", None)

    async def broadcast_messages(self, *messages: str) -> None:
        commands = []
        for message in messages:
            styled = style_console_message(message)
            if styled:
                commands.append(
                    f"CONSOLE_MESSAGE {readline_console_text(styled)}"
                )
        if commands:
            await self.sink.send(*commands)

    async def broadcast(self, message: str) -> None:
        await self.broadcast_messages(message)

    async def result_message(self, message: str) -> None:
        """Deliver race-result chatter only to players who opted in."""
        delivered: set[str] = set()
        preferences = getattr(self, "result_message_preferences", {})
        for player in list(self.players.values()):
            if (
                not player.connected
                or player.is_ai
                or player.identity_key in delivered
                or preferences.get(player.identity_key, True) is False
            ):
                continue
            delivered.add(player.identity_key)
            await self.private(player, message)

    async def _write_dashboard_chat(self, message: dict[str, object]) -> None:
        try:
            dashboard = getattr(self, "live_dashboard_chat", None)
            if dashboard is None:
                return
            await asyncio.to_thread(dashboard.publish_chat, message)
        except asyncio.CancelledError:
            raise
        except Exception:
            LOG.exception("unable to publish live dashboard chat")

    async def _write_dashboard_activity(self, finish: dict[str, object]) -> None:
        try:
            dashboard = getattr(self, "live_dashboard_chat", None)
            if dashboard is None:
                return
            await asyncio.to_thread(dashboard.publish_activity, finish)
        except asyncio.CancelledError:
            raise
        except Exception:
            LOG.exception("unable to publish live dashboard activity")

    async def _write_admin_audit(self, event: dict[str, object]) -> None:
        try:
            dashboard = getattr(self, "live_dashboard_chat", None)
            if dashboard is None:
                return
            await asyncio.to_thread(
                dashboard.publish_admin_audit,
                self.server_id,
                event,
            )
        except asyncio.CancelledError:
            raise
        except Exception:
            LOG.exception("unable to publish private player audit event")

    def _publish_player_audit(
        self,
        action: str,
        player: Player,
        **details: object,
    ) -> None:
        if getattr(self, "live_dashboard_chat", None) is None or player.is_ai:
            return
        live_config = self.config.get("live_dashboard", {})
        event: dict[str, object] = {
            "action": action,
            "region": clean_console_text(
                str(live_config.get("local_region", "LOCAL"))
            )[:16],
            "playerId": public_player_id(player.identity_key),
            "logName": plain_console_text(player.log_name).strip()[:128],
            "displayName": plain_console_text(player.display_name).strip()[:128],
            "authName": plain_console_text(player.auth_name or "").strip()[:128],
            "ipAddress": clean_console_text(
                getattr(player, "ip_address", "")
            )[:128],
            "active": bool(player.active),
            "authenticated": bool(player.auth_name),
            **details,
        }
        task = asyncio.create_task(
            self._write_admin_audit(event),
            name=f"admin-audit-{action}",
        )
        self._live_dashboard_tasks.add(task)
        task.add_done_callback(self._live_dashboard_tasks.discard)

    def _publish_dashboard_map_change(self, previous_key: str) -> None:
        if (
            getattr(self, "live_dashboard", None) is None
            or getattr(self, "live_dashboard_chat", None) is None
            or self.current is None
            or not previous_key
            or previous_key == self.current.key
        ):
            return
        live_config = self.config.get("live_dashboard", {})
        payload = {
            **self._dashboard_map_metadata(self.current),
            "kind": "map_change",
            "mapName": self.current.name,
            "serverId": clean_console_text(self.server_id)[:32],
            "region": clean_console_text(
                str(live_config.get("local_region", "LOCAL"))
            )[:16],
        }
        task = asyncio.create_task(
            self._write_dashboard_activity(payload),
            name="live-dashboard-map-change",
        )
        self._live_dashboard_tasks.add(task)
        task.add_done_callback(self._live_dashboard_tasks.discard)

    def _publish_dashboard_chat(
        self,
        server_id: str,
        region: str,
        name: str,
        message: str,
        authenticated: bool,
    ) -> None:
        if getattr(self, "live_dashboard_chat", None) is None:
            return
        clean_message = clean_console_text(message).strip()
        if not clean_message or clean_message.startswith("/"):
            return
        task = asyncio.create_task(
            self._write_dashboard_chat({
                "kind": "chat",
                "serverId": clean_console_text(server_id)[:32],
                "region": clean_console_text(region)[:16],
                "name": plain_console_text(name).strip()[:128] or "Player",
                "message": plain_console_text(clean_message).strip()[:512],
                "authenticated": bool(authenticated),
            }),
            name="live-dashboard-chat",
        )
        self._live_dashboard_tasks.add(task)
        task.add_done_callback(self._live_dashboard_tasks.discard)

    def _publish_dashboard_presence(self, action: str, player: Player) -> None:
        if (
            getattr(self, "live_dashboard_chat", None) is None
            or action not in {"join", "leave"}
            or player.is_ai
        ):
            return
        live_config = self.config.get("live_dashboard", {})
        if action == "join":
            message = "entered the game." if player.active else "entered as spectator."
        else:
            message = "left the game." if player.active else "left as spectator."
        task = asyncio.create_task(
            self._write_dashboard_chat({
                "kind": action,
                "serverId": clean_console_text(self.server_id)[:32],
                "region": clean_console_text(
                    str(live_config.get("local_region", "LOCAL"))
                )[:16],
                "name": plain_console_text(player.display_name).strip()[:128]
                or "Player",
                "message": message,
                "authenticated": bool(player.auth_name),
            }),
            name=f"live-dashboard-{action}",
        )
        self._live_dashboard_tasks.add(task)
        task.add_done_callback(self._live_dashboard_tasks.discard)
        self._publish_player_audit(action, player, message=message)

    def _publish_dashboard_finish_activity(
        self,
        player: Player,
        *,
        seconds: float,
        rank: int,
        turns: int | None,
        improved: bool,
        best_seconds: float,
        best_turns: int | None,
        previous_best: float | None,
        previous_best_turns: int | None,
        pb_rank: int | None,
        no_cp_seconds: float | None,
        no_cp_rank: int | None,
    ) -> None:
        if getattr(self, "live_dashboard_chat", None) is None or self.current is None:
            return
        reference_seconds = (
            previous_best
            if improved and previous_best is not None
            else None if improved else best_seconds
        )
        reference_turns = (
            previous_best_turns
            if improved and previous_best is not None
            else None if improved else best_turns
        )
        live_config = self.config.get("live_dashboard", {})
        payload = {
            **self._dashboard_map_metadata(self.current),
            "kind": "finish",
            "mapName": self.current.name,
            "serverId": clean_console_text(self.server_id)[:32],
            "region": clean_console_text(
                str(live_config.get("local_region", "LOCAL"))
            )[:16],
            "playerId": public_player_id(player.identity_key),
            "name": plain_console_text(player.record_name).strip()[:128] or "Player",
            "authenticated": bool(player.auth_name),
            "seconds": round(seconds, 6),
            "rank": max(1, int(rank)),
            "referenceRank": None if pb_rank is None else max(1, int(pb_rank)),
            "referenceSeconds": (
                None if reference_seconds is None else round(reference_seconds, 6)
            ),
            "splitSeconds": (
                None
                if reference_seconds is None
                else round(seconds - reference_seconds, 6)
            ),
            "noCheckpointSeconds": (
                None if no_cp_seconds is None else round(no_cp_seconds, 6)
            ),
            "noCheckpointRank": (
                None if no_cp_rank is None else max(1, int(no_cp_rank))
            ),
            "noCheckpointSplitSeconds": (
                None
                if no_cp_seconds is None
                else round(no_cp_seconds - best_seconds, 6)
            ),
            "turns": turns,
            "referenceTurns": reference_turns,
            "turnsSplit": (
                None
                if turns is None or reference_turns is None
                else turns - reference_turns
            ),
            "personalBest": bool(improved),
        }
        task = asyncio.create_task(
            self._write_dashboard_activity(payload),
            name="live-dashboard-finish",
        )
        self._live_dashboard_tasks.add(task)
        task.add_done_callback(self._live_dashboard_tasks.discard)
        self._publish_player_audit(
            "finish",
            player,
            mapKey=payload.get("mapKey", ""),
            mapName=payload.get("mapName", ""),
            seconds=payload["seconds"],
            turns=turns,
            rank=payload["rank"],
            personalBest=bool(improved),
        )

    def _dashboard_map_metadata(self, entry: MapEntry | None) -> dict[str, object]:
        if entry is None:
            return {}
        return {
            "mapKey": map_records_key(entry),
            "resourcePath": entry.key,
            "mapId": entry.map_id,
            "revisionId": entry.revision_id,
            "name": entry.name,
            "author": entry.author,
            "version": entry.version,
            "storagePath": entry.storage_path,
            "sizeFactor": round(float(self.current_size_factor or 0), 6),
            "checkpointCount": len(entry.checkpoint_ids),
            "checkpointMode": entry.checkpoint_mode,
        }

    def _dashboard_current_map_metadata(self) -> dict[str, object]:
        metadata = self._dashboard_map_metadata(self.current)
        if not metadata or self.current is None:
            return metadata
        selection = dict(getattr(self, "current_map_selection", {}))
        if selection.get("resourcePath") != self.current.key:
            selection = {}
        metadata.update({
            "queued": bool(selection.get("queued", False)),
            "queuedBy": plain_console_text(
                selection.get("queuedBy", "")
            ).strip()[:128],
            "queuedVia": clean_console_text(
                selection.get("queuedVia", "rotation")
            )[:32] or "rotation",
            "queuedAt": max(0, int(selection.get("queuedAt", 0) or 0)),
        })
        return metadata

    def _remember_previous_map(self, entry: MapEntry | None) -> None:
        metadata = self._dashboard_map_metadata(entry)
        if not metadata:
            return
        now_ms = int(time.time() * 1000)
        selection = dict(getattr(self, "current_map_selection", {}))
        history_entry = {
            **metadata,
            "startedAt": max(
                0,
                int(
                    selection.get("selectedAt")
                    or ((getattr(self, "round_started_epoch", None) or 0) * 1000)
                ),
            ),
            "endedAt": now_ms,
            "queued": bool(selection.get("queued", False)),
            "queuedBy": plain_console_text(
                selection.get("queuedBy", "")
            ).strip()[:128],
            "queuedVia": clean_console_text(
                selection.get("queuedVia", "rotation")
            )[:32] or "rotation",
        }
        self.previous_map_metadata = history_entry
        if not hasattr(self, "map_history"):
            self.map_history = collections.deque(maxlen=MAP_HISTORY_LIMIT)
        self.map_history.appendleft(history_entry)
        self.store.set_json("previous_map_metadata", history_entry)
        self.store.set_json("map_history", list(self.map_history))

    def _dashboard_players(
        self,
    ) -> tuple[list[dict[str, object]], dict[str, list[dict[str, object]]]]:
        local = [
            {
                "playerId": public_player_id(player.identity_key),
                "name": plain_console_text(player.display_name).strip()[:128],
                "active": bool(player.active),
                "alive": bool(player.alive),
                "authenticated": bool(player.auth_name),
            }
            for player in self.players.values()
            if player.connected and not player.is_ai
        ]
        key = lambda item: (not bool(item["active"]), str(item["name"]).casefold())
        return sorted(local, key=key), {}

    def _dashboard_live_state(self) -> dict[str, object]:
        live_config = self.config.get("live_dashboard", {})
        local_players, _ = self._dashboard_players()
        now = time.time()
        time_left = max(0, int((self.deadline_epoch or now) - now))
        map_metadata = self._dashboard_current_map_metadata()
        current_records = self.store.records(map_records_key(self.current)) if self.current else []
        replay_player_ids = self.store.dashboard_replay_player_ids(
            map_records_key(self.current)
        ) if self.current else set()
        current_leaderboard = [
            {
                "rank": rank,
                "playerId": public_player_id(record.identity_key),
                "name": record.username[:128],
                "seconds": round(record.best_seconds, 6),
                "turns": record.best_turns,
                "authenticated": record.authenticated,
                "achievedAt": (
                    int(record.achieved_at * 1000)
                    if record.achieved_at is not None else None
                ),
                "hasReplay": public_player_id(record.identity_key) in replay_player_ids,
            }
            for rank, record in enumerate(current_records[:10], 1)
        ]
        upcoming_rotation = self._dashboard_upcoming_rotation()
        return {
            "map": map_metadata,
            "previousMap": dict(self.previous_map_metadata),
            "nextMap": dict(upcoming_rotation[0]) if upcoming_rotation else {},
            "mapHistory": list(self.map_history),
            "upcomingRotation": upcoming_rotation,
            "roundActive": self._round_is_active(),
            "timeRemainingSeconds": time_left,
            "leaderboard": current_leaderboard,
            "servers": {
                self.server_id: {
                    "id": self.server_id,
                    "region": str(live_config.get("local_region", "LOCAL"))[:16],
                    "online": True,
                    "mapKey": map_records_key(self.current) if self.current else "",
                    "players": local_players,
                },
            },
        }

    def _server_management_status(self) -> dict[str, object]:
        now_epoch = time.time()
        now_monotonic = time.monotonic()
        unique_players = {
            id(player): player
            for player in self.players.values()
            if player.connected and not player.is_ai
        }.values()
        players = [
            {
                "target": clean_console_text(player.target)[:128],
                "playerId": public_player_id(player.identity_key),
                "name": plain_console_text(player.display_name).strip()[:128],
                "authName": plain_console_text(player.auth_name or "").strip()[:128],
                "ipAddress": clean_console_text(
                    getattr(player, "ip_address", "")
                )[:128],
                "active": bool(player.active),
                "alive": bool(player.alive),
                "afk": bool(player.afk),
                "activityAgeSeconds": round(
                    max(0.0, now_monotonic - player.last_turn_monotonic), 1
                ) if player.last_turn_monotonic is not None else None,
            }
            for player in unique_players
        ]
        players.sort(key=lambda item: (
            not bool(item["active"]), str(item["name"]).casefold()
        ))
        queued = []
        for position, key in enumerate(list(self.queue)[:25], 1):
            entry = self.repository.catalog.get(key)
            attribution = getattr(self, "queue_attribution", {}).get(key, {})
            queued.append({
                "position": position,
                "mapKey": key,
                "name": self._display_map_name(entry) if entry else key,
                "author": entry.author if entry else "Unknown",
                "version": entry.version if entry else "",
                "queued": True,
                "queuedBy": str(attribution.get("queuedBy", "Unknown"))[:128],
                "queuedVia": str(attribution.get("queuedVia", "server"))[:32],
                "queuedAt": max(0, int(attribution.get("queuedAt", 0) or 0)),
            })
        try:
            disk = shutil.disk_usage(self.store.path.parent)
            disk_free = int(disk.free)
            disk_total = int(disk.total)
        except OSError:
            disk_free = 0
            disk_total = 0
        try:
            database_bytes = int(self.store.path.stat().st_size)
        except OSError:
            database_bytes = 0
        try:
            load_one, load_five, load_fifteen = os.getloadavg()
        except OSError:
            load_one = load_five = load_fifteen = 0.0
        game_event_age = (
            max(0.0, now_monotonic - self.last_game_monotonic)
            if self.last_game_monotonic is not None else None
        )
        return {
            "region": str(
                self.config.get("live_dashboard", {}).get("local_region", "")
            )[:16],
            "online": True,
            "role": "standalone",
            "pid": os.getpid(),
            "startedAt": int(self.started_at_epoch * 1000),
            "uptimeSeconds": max(0, int(now_epoch - self.started_at_epoch)),
            "roundActive": self._round_is_active(),
            "transitioning": bool(self.transitioning),
            "finalCountdownActive": bool(self.final_countdown_active),
            "serverRestartActive": bool(
                getattr(self, "server_restart_active", False)
            ),
            "serverScriptReloadPending": bool(self.controller_reload_state.get("pending")),
            # Compatibility for a web release still open during deployment.
            "controllerReloadPending": bool(self.controller_reload_state.get("pending")),
            "respawnsPaused": bool(self.respawns_paused),
            "timeRemainingSeconds": max(
                0, int((self.deadline_epoch or now_epoch) - now_epoch)
            ),
            "roundStartedAt": int(self.round_started_epoch * 1000)
            if self.round_started_epoch else None,
            "map": self._dashboard_map_metadata(self.current),
            "nextMap": self._dashboard_map_metadata(self._peek_next()),
            "players": players,
            "playerCount": len(players),
            "activePlayerCount": sum(bool(player["active"]) for player in players),
            "alivePlayerCount": sum(bool(player["alive"]) for player in players),
            "queue": queued,
            "queueCount": len(self.queue),
            "rotationRemaining": len(self.rotation),
            "catalogMapCount": len(self.repository.catalog),
            "excludedMapCount": len(self.excluded_map_keys),
            "catalogVersion": int(self.repository.firebase_catalog_version),
            "gameEventAgeSeconds": round(game_event_age, 2)
            if game_event_age is not None else None,
            "consoleAvailable": bool(
                getattr(self, "server_console_available", False)
            ),
            "consoleStreamActive": bool(
                time.monotonic()
                < getattr(self, "server_console_stream_until_monotonic", 0.0)
            ),
            "system": {
                "load1": round(load_one, 3),
                "load5": round(load_five, 3),
                "load15": round(load_fifteen, 3),
                "cpuCount": int(os.cpu_count() or 1),
                "maxResidentBytes": int(resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
                * 1024,
                "databaseBytes": database_bytes,
                "diskFreeBytes": disk_free,
                "diskTotalBytes": disk_total,
            },
        }

    @staticmethod
    def _server_management_field(
        command: dict[str, object],
        name: str,
        maximum: int,
    ) -> str:
        return clean_console_text(command.get(name, "")).strip()[:maximum]

    def _server_management_player(self, command: dict[str, object]) -> Player:
        uid = re.sub(
            r"[^A-Za-z0-9_-]", "_",
            self._server_management_field(command, "requestedBy", 128),
        )[:64] or "admin"
        name = plain_console_text(
            self._server_management_field(command, "requestedName", 80)
        ).strip() or "Web admin"
        return Player(f"web-admin-{uid}", name, auth_name=name, active=False)


    @staticmethod
    def _sanitize_server_console_line(value: object) -> str:
        text = plain_console_text(value).replace("\x00", "").strip()
        text = re.sub(
            r"^\[\d{4}/\d{2}/\d{2}-\d{2}:\d{2}:\d{2}\]\s*",
            "",
            text,
        )
        if not text:
            return ""
        if SERVER_CONSOLE_SENSITIVE_RE.search(text):
            return "[sensitive console output withheld]"
        return text[:600]

    def _record_server_console_line(self, value: object) -> None:
        message = self._sanitize_server_console_line(value)
        if not message:
            return
        self.server_console_sequence += 1
        self.server_console_entries.append({
            "sequence": self.server_console_sequence,
            "at": int(time.time() * 1000),
            "message": message,
        })

    async def follow_server_console(self) -> None:
        live_config = self.config.get("live_dashboard", {})
        if (
            self.live_dashboard_chat is None
            or not isinstance(live_config, dict)
            or live_config.get("management_enabled") is not True
        ):
            return
        await self.sink.send("CONSOLE_LOG 1")
        path = self.server_console_path
        handle = None
        inode = None
        first_open = True
        while not self.stop_event.is_set():
            try:
                stat = path.stat()
                if (
                    handle is None
                    or inode != stat.st_ino
                    or handle.tell() > stat.st_size
                ):
                    if handle:
                        handle.close()
                    handle = path.open("rb")
                    if first_open and stat.st_size > 131_072:
                        handle.seek(stat.st_size - 131_072)
                        handle.readline()
                    inode = stat.st_ino
                    first_open = False
                self.server_console_available = True
                raw_line = handle.readline()
                if raw_line:
                    self._record_server_console_line(
                        self._decode_game_bytes(raw_line, "server console")
                    )
                    continue
                if (
                    stat.st_size > SERVER_CONSOLE_MAX_FILE_BYTES
                    and handle.tell() >= stat.st_size
                ):
                    handle.close()
                    handle = None
                    inode = None
                    path.write_bytes(b"")
            except FileNotFoundError:
                self.server_console_available = False
            except OSError:
                self.server_console_available = False
                LOG.exception("following the game console log failed")
            await asyncio.sleep(0.05)
        if handle:
            handle.close()

    async def _publish_server_console(self, dashboard, server_id: str) -> None:
        if (
            time.monotonic()
            >= getattr(self, "server_console_stream_until_monotonic", 0.0)
        ):
            return
        last_sequence = getattr(
            self, "server_console_last_published_sequence", 0
        )
        entries = [
            dict(entry)
            for entry in getattr(self, "server_console_entries", ())
            if int(entry.get("sequence", 0)) > last_sequence
        ][:SERVER_CONSOLE_BATCH_SIZE]
        if not entries:
            return
        await asyncio.to_thread(
            dashboard.publish_admin_console, server_id, entries
        )
        self.server_console_last_published_sequence = int(
            entries[-1]["sequence"]
        )

    async def _execute_server_management_command(
        self,
        command: dict[str, object],
    ) -> tuple[str, dict[str, object]]:
        command_type = self._server_management_field(command, "type", 64)
        if command_type not in SERVER_MANAGEMENT_COMMANDS:
            raise ValueError("That server-management command is not supported.")
        actor = self._server_management_player(command)
        target = self._server_management_field(command, "target", 128)
        message = self._server_management_field(command, "message", 512)
        reason = self._server_management_field(command, "reason", 240)
        map_key = self._server_management_field(command, "mapKey", 1024)

        if command_type == "announce":
            if not message:
                raise ValueError("Enter an announcement.")
            await self.broadcast(message)
            return "Announcement delivered.", {"scope": "local"}

        if command_type == "web_chat":
            display_name = normalize_console_colors(target[:80])
            plain_name = plain_console_text(display_name).strip()
            plain_message = plain_console_text(message).strip()
            if not plain_name:
                raise ValueError("Enter a web chat display name.")
            if not plain_message:
                raise ValueError("Enter a chat message.")
            rendered = (
                f"{COLOR_COMMAND}[Web] {display_name}{COLOR_CHAT}: "
                f"{plain_message}"
            )
            await self.sink.send(
                f"CONSOLE_MESSAGE {readline_console_text(rendered)}"
            )
            live_config = self.config.get("live_dashboard", {})
            await self._write_dashboard_chat({
                "kind": "web_chat",
                "serverId": clean_console_text(self.server_id)[:32],
                "region": clean_console_text(
                    str(live_config.get("local_region", "LOCAL"))
                )[:16],
                "name": plain_name[:128],
                "coloredName": display_name,
                "message": plain_message[:512],
                "authenticated": True,
            })
            await self._write_admin_audit({
                "action": "website_chat",
                "region": clean_console_text(
                    str(live_config.get("local_region", "LOCAL"))
                )[:16],
                "websiteUid": self._server_management_field(
                    command, "requestedBy", 128
                ),
                "websiteName": self._server_management_field(
                    command, "requestedName", 80
                ),
                "displayName": plain_name[:128],
                "message": plain_message[:512],
                "authenticated": True,
            })
            return (
                f"Web chat message delivered as {plain_name}.",
                {"displayName": plain_name},
            )

        if command_type == "start_console_stream":
            now = time.monotonic()
            if now >= getattr(
                self, "server_console_stream_until_monotonic", 0.0
            ):
                sequence = getattr(self, "server_console_sequence", 0)
                self.server_console_last_published_sequence = max(
                    0, sequence - SERVER_CONSOLE_INITIAL_LINES
                )
            self.server_console_stream_until_monotonic = max(
                getattr(self, "server_console_stream_until_monotonic", 0.0),
                now + SERVER_CONSOLE_STREAM_SECONDS,
            )
            return (
                "Live console stream enabled for 90 seconds.",
                {"streamSeconds": int(SERVER_CONSOLE_STREAM_SECONDS)},
            )

        if command_type == "direct_message":
            player = self.player_for(target)
            if player is None or not player.connected:
                raise ValueError("That player is no longer connected to this server.")
            if not message:
                raise ValueError("Enter a private message.")
            await self.private(player, message)
            return f"Message delivered to {plain_console_text(player.display_name)}.", {}

        if command_type in {"kick", "ban", "silence", "voice", "kill"}:
            player = self.player_for(target)
            if player is None or not player.connected:
                raise ValueError("That player is no longer connected to this server.")
            game_target = quote_console(player.target)
            display_name = plain_console_text(player.display_name).strip()
            if command_type == "kick":
                await self.sink.send(
                    f"KICK {game_target} {readline_console_text(reason or 'Removed by a server administrator')}"
                )
            elif command_type == "ban":
                duration = max(1, min(int(command.get("durationMinutes", 60) or 60), 10_080))
                await self.sink.send(
                    f"BAN {game_target} {duration} {readline_console_text(reason or 'Banned by a server administrator')}"
                )
                return f"Banned {display_name} for {duration} minutes.", {"durationMinutes": duration}
            elif command_type == "silence":
                await self.sink.send(f"SILENCE {game_target}")
            elif command_type == "voice":
                await self.sink.send(f"VOICE {game_target}")
            else:
                await self.sink.send(f"KILL {game_target}")
            past = {
                "kick": "Kicked", "silence": "Silenced",
                "voice": "Unsilenced", "kill": "Killed",
            }[command_type]
            return f"{past} {display_name}.", {}

        if command_type in {"queue_map", "remove_queued_map", "change_map"}:
            entry = self.repository.find_by_spec(map_key)
            if entry is None or entry.key not in self.repository.catalog:
                raise ValueError("That map is not in the active server catalog.")
            if command_type == "remove_queued_map":
                if entry.key not in self.queue:
                    raise ValueError("That map is not currently queued.")
                self.queue.remove(entry.key)
                getattr(self, "queue_attribution", {}).pop(entry.key, None)
                self._save_rotation()
                return f"Removed {self._display_map_name(entry)} from the queue.", {}
            if self.current and entry.key == self.current.key:
                raise ValueError("That map is already active.")
            with contextlib.suppress(ValueError):
                self.queue.remove(entry.key)
            if command_type == "change_map":
                self.queue.appendleft(entry.key)
                self._attribute_queued_map(
                    entry.key, actor.record_name, "website"
                )
                self._save_rotation()
                await self.broadcast(
                    f"{actor.record_name} selected {self._display_map_name(entry)} by {entry.author}."
                )
                await self.activate_next_map("admin web console")
                return f"Changing to {self._display_map_name(entry)}.", {"mapKey": entry.key}
            self.queue.append(entry.key)
            self._attribute_queued_map(
                entry.key, actor.record_name, "website"
            )
            self._save_rotation()
            await self.broadcast(
                f"{actor.record_name} queued {self._display_map_name(entry)} by {entry.author} "
                f"(position {len(self.queue)})."
            )
            return f"Queued {self._display_map_name(entry)} at position {len(self.queue)}.", {"mapKey": entry.key}

        if command_type == "clear_queue":
            count = len(self.queue)
            self.queue.clear()
            self.queue_attribution = {}
            self._save_rotation()
            if count:
                await self.broadcast(f"{actor.record_name} cleared {count} map(s) from the queue.")
            return f"Cleared {count} queued map(s).", {"removed": count}

        if command_type == "force_skip":
            if self.transitioning:
                raise ValueError("A map change is already in progress.")
            self._clear_vote("skip")
            await self.broadcast(f"{actor.record_name} force-skipped the map.")
            await self.activate_next_map("admin web console force skip")
            return "Advanced to the next map.", {}

        if command_type == "end_map":
            if not self.current or not self._round_is_active():
                raise ValueError("There is no active map to end.")
            if self.transitioning or self.final_countdown_active:
                raise ValueError("A map transition or final countdown is already active.")
            self.final_countdown_announcement = None
            self.deadline_epoch = time.time()
            self.store.set_json("deadline_epoch", self.deadline_epoch)
            return "Started the end-of-map sequence.", {}

        if command_type == "reload_maps":
            async with self.map_lock:
                before = set(self.repository.catalog)
                await asyncio.to_thread(self.repository.sync, True)
                self._reconcile_rotation()
                after = set(self.repository.catalog)
            return (
                f"Reloaded {len(after)} maps ({len(after - before)} added, "
                f"{len(before - after)} removed).",
                {"mapCount": len(after), "added": len(after - before), "removed": len(before - after)},
            )

        if command_type == "restart_round":
            if self.transitioning:
                raise ValueError("A map transition is already in progress.")
            self._reset_attempts()
            await self.sink.send("START_NEW_MATCH", "KILL_ALL")
            await self.broadcast(f"{actor.record_name} restarted the round.")
            return "Round restart requested.", {}

        if command_type == "restart_server":
            duration = self.request_server_restart(actor.record_name)
            if duration is None:
                raise ValueError(
                    "The server cannot start a restart countdown during another "
                    "transition, countdown, or reload."
                )
            return (
                f"Server restart countdown started for {math.ceil(duration)} seconds.",
                {"countdownSeconds": math.ceil(duration)},
            )

        if command_type == "console_command":
            raw_message = command.get("message")
            if not isinstance(raw_message, str) or not raw_message.strip():
                raise ValueError("Enter one server console command.")
            if "\r" in raw_message or "\n" in raw_message:
                raise ValueError("Server console commands must contain one line.")
            console_command = raw_message.strip()
            if len(console_command) > 512:
                raise ValueError("Server console commands are limited to 512 characters.")
            await self.sink.send(console_command)
            return "Server console command sent.", {
                "command": clean_console_text(console_command)[:512]
            }

        if command_type == "set_engine_option":
            option = self._server_management_field(command, "option", 64).upper()
            if option not in SERVER_MANAGEMENT_ENGINE_OPTIONS:
                raise ValueError("That engine option is not available in the web console.")
            try:
                value = float(command.get("value"))
            except (TypeError, ValueError) as exc:
                raise ValueError("Enter a numeric engine-option value.") from exc
            minimum, maximum = SERVER_MANAGEMENT_ENGINE_OPTIONS[option]
            if not math.isfinite(value) or not minimum <= value <= maximum:
                raise ValueError(f"{option} must be between {minimum:g} and {maximum:g}.")
            rendered = f"{value:.9g}"
            await self.sink.send(f"{option} {rendered}")
            return f"Set {option} to {rendered} until the server is restarted or reconfigured.", {"option": option, "value": value}

        if command_type in {"reload_server_script", "reload_controller"}:
            if not self.request_controller_reload(actor.record_name):
                raise ValueError("A graceful server script reload is already pending.")
            return "Graceful server script reload scheduled after active runs finish.", {}

        raise ValueError("That server-management command is not implemented.")

    async def server_management_worker(self) -> None:
        live_config = self.config.get("live_dashboard", {})
        dashboard = self.live_dashboard_chat
        if (
            dashboard is None
            or not isinstance(live_config, dict)
            or live_config.get("management_enabled") is not True
        ):
            return
        server_id = self.server_id
        next_status = 0.0
        next_prune = 0.0
        while not self.stop_event.is_set():
            try:
                monotonic_now = time.monotonic()
                if monotonic_now >= next_status:
                    status = self._server_management_status()
                    await asyncio.to_thread(
                        dashboard.publish_admin_status, server_id, status
                    )
                    next_status = monotonic_now + 15.0
                commands = await asyncio.to_thread(
                    dashboard.queued_admin_commands, server_id
                )
                for command_id, command in commands:
                    expires_at = int(command.get("expiresAt", 0) or 0)
                    if expires_at <= int(time.time() * 1000):
                        await asyncio.to_thread(
                            dashboard.update_admin_command,
                            server_id,
                            command_id,
                            "expired",
                            result="Command expired before the server could safely execute it.",
                        )
                        continue
                    await asyncio.to_thread(
                        dashboard.update_admin_command,
                        server_id,
                        command_id,
                        "running",
                        result="Server accepted the command.",
                    )
                    try:
                        result, details = await self._execute_server_management_command(command)
                    except Exception as exc:
                        LOG.warning(
                            "admin command failed: server=%s id=%s type=%s error=%s",
                            server_id, command_id, command.get("type"), exc,
                        )
                        await asyncio.to_thread(
                            dashboard.update_admin_command,
                            server_id,
                            command_id,
                            "failed",
                            result=str(exc),
                        )
                        await self._write_admin_audit({
                            "action": "admin_command_failed",
                            "region": clean_console_text(
                                str(live_config.get("local_region", "LOCAL"))
                            )[:16],
                            "websiteUid": command.get("requestedBy", ""),
                            "websiteName": command.get("requestedName", ""),
                            "command": command.get("type", ""),
                            "target": command.get("target", ""),
                            "result": str(exc),
                        })
                    else:
                        LOG.info(
                            "admin command completed: server=%s id=%s type=%s actor=%s",
                            server_id, command_id, command.get("type"),
                            command.get("requestedBy"),
                        )
                        await asyncio.to_thread(
                            dashboard.update_admin_command,
                            server_id,
                            command_id,
                            "succeeded",
                            result=result,
                            details=details,
                        )
                        await self._write_admin_audit({
                            "action": "admin_command",
                            "region": clean_console_text(
                                str(live_config.get("local_region", "LOCAL"))
                            )[:16],
                            "websiteUid": command.get("requestedBy", ""),
                            "websiteName": command.get("requestedName", ""),
                            "command": command.get("type", ""),
                            "target": command.get("target", ""),
                            "result": result,
                        })
                await self._publish_server_console(dashboard, server_id)
                if monotonic_now >= next_prune:
                    await asyncio.to_thread(
                        dashboard.prune_admin_commands, server_id
                    )
                    next_prune = monotonic_now + 300.0
            except asyncio.CancelledError:
                raise
            except Exception:
                LOG.exception("server management worker failed")
            try:
                await asyncio.wait_for(self.stop_event.wait(), timeout=2.0)
            except TimeoutError:
                pass

    def _apply_website_rating_command(
        self, command: dict[str, object]
    ) -> str:
        if int(command.get("schemaVersion", 0) or 0) != 1:
            raise ValueError("Unsupported rating-command version.")
        rating_key = unicodedata.normalize(
            "NFKC", str(command.get("ratingKey", ""))
        ).strip()
        active_rating_keys = {
            entry.rating_key for entry in self.repository.catalog.values()
        }
        if rating_key not in active_rating_keys:
            raise ValueError("That map is no longer available to rate.")
        try:
            rating = int(command.get("rating", 0))
            requested_at_ms = int(command.get("requestedAt", 0))
        except (TypeError, ValueError) as exc:
            raise ValueError("The rating command is malformed.") from exc
        if not 1 <= rating <= 5:
            raise ValueError("Choose a rating from 1 to 5.")
        now_ms = int(time.time() * 1000)
        if (
            requested_at_ms < now_ms - 10 * 60 * 1000
            or requested_at_ms > now_ms + 60 * 1000
        ):
            raise ValueError("The rating command has expired.")
        website_uid = str(command.get("websiteUid", ""))
        if not re.fullmatch(r"[A-Za-z0-9_-]{1,128}", website_uid):
            raise ValueError("The website account identity is invalid.")
        display_name = unicodedata.normalize(
            "NFKC", str(command.get("displayName", ""))
        ).strip()
        game_username = unicodedata.normalize(
            "NFKC", str(command.get("gameUsername", ""))
        ).strip()
        if (
            len(display_name) > 40
            or len(game_username) > 64
            or any(
                ord(character) < 32 or ord(character) == 127
                for character in display_name + game_username
            )
        ):
            raise ValueError("The rating account name is invalid.")
        website_identity = f"web:{website_uid}"
        if game_username:
            identity_key = f"auth:{game_username.casefold()}"
            username = game_username
            if identity_key != website_identity:
                self.store.revoke_rating(rating_key, website_identity)
        else:
            identity_key = website_identity
            username = display_name or "Racer"
        self.store.set_rating_identity(
            rating_key,
            identity_key,
            username,
            True,
            rating,
            rated_at=requested_at_ms / 1000.0,
        )
        self.live_dashboard_refresh_requested = True
        return f"Rated map {rating}/5."

    async def website_rating_worker(self) -> None:
        dashboard = self.live_dashboard
        if dashboard is None:
            return
        server_id = self.server_id
        next_prune = 0.0
        while not self.stop_event.is_set():
            try:
                commands = await asyncio.to_thread(
                    dashboard.queued_rating_commands, server_id
                )
                for command_id, command in commands:
                    expires_at = int(command.get("expiresAt", 0) or 0)
                    if expires_at <= int(time.time() * 1000):
                        await asyncio.to_thread(
                            dashboard.update_rating_command,
                            server_id,
                            command_id,
                            "expired",
                            result="Rating expired before it could be applied.",
                        )
                        continue
                    await asyncio.to_thread(
                        dashboard.update_rating_command,
                        server_id,
                        command_id,
                        "running",
                        result="Rating accepted by the server.",
                    )
                    try:
                        result = self._apply_website_rating_command(command)
                    except Exception as exc:
                        LOG.warning(
                            "website rating failed: server=%s id=%s error=%s",
                            server_id,
                            command_id,
                            exc,
                        )
                        await asyncio.to_thread(
                            dashboard.update_rating_command,
                            server_id,
                            command_id,
                            "failed",
                            result=str(exc),
                        )
                    else:
                        await asyncio.to_thread(
                            dashboard.update_rating_command,
                            server_id,
                            command_id,
                            "succeeded",
                            result=result,
                        )
                monotonic_now = time.monotonic()
                if monotonic_now >= next_prune:
                    await asyncio.to_thread(
                        dashboard.prune_rating_commands, server_id
                    )
                    next_prune = monotonic_now + 300.0
            except asyncio.CancelledError:
                raise
            except Exception:
                LOG.exception("website rating worker failed")
            try:
                await asyncio.wait_for(self.stop_event.wait(), timeout=2.0)
            except TimeoutError:
                pass

    def _dashboard_maps_by_record_key(self) -> dict[str, dict[str, object]]:
        ratings = self.store.rating_summaries()
        rating_entries = self.store.rating_entries_by_map()
        return {
            map_records_key(entry): {
                "mapId": entry.map_id,
                "name": entry.name,
                "author": entry.author,
                "version": entry.version,
                "storagePath": entry.storage_path,
                "ratingKey": entry.rating_key,
                "rating": ratings.get(entry.rating_key, (None, 0))[0],
                "ratingCount": ratings.get(entry.rating_key, (None, 0))[1],
                "ratings": rating_entries.get(entry.rating_key, []),
            }
            for entry in self.repository.catalog.values()
            if entry.storage_path
        }

    def _replay_record_key_aliases(self) -> dict[str, str]:
        aliases = {
            entry.key: map_records_key(entry)
            for entry in self.repository.catalog.values()
            if entry.key and map_records_key(entry) != entry.key
        }
        for resource_key, metadata in self.repository.firebase_maps_by_key.items():
            record_key = str(metadata.get("recordKey") or "").strip()
            if resource_key and record_key and resource_key != record_key:
                aliases[resource_key] = record_key
        return aliases

    async def live_dashboard_publisher(self) -> None:
        if self.live_dashboard is None:
            return
        next_leaderboards = 0.0
        while not self.stop_event.is_set():
            try:
                state = self._dashboard_live_state()
                await asyncio.to_thread(self.live_dashboard.publish_live, state)
                replay_writes = await asyncio.to_thread(
                    self.live_dashboard.publish_replay_batch,
                    self.server_id,
                )
                if replay_writes:
                    LOG.info("published %d racing replay(s)", replay_writes)
                history_writes = await asyncio.to_thread(
                    self.live_dashboard.publish_replay_history_backfill_batch,
                    self.server_id,
                )
                if history_writes:
                    LOG.info(
                        "refreshed %d racing replay histor%s with exact map revisions",
                        history_writes,
                        "y" if history_writes == 1 else "ies",
                    )
                now = time.monotonic()
                if now >= next_leaderboards or self.live_dashboard_refresh_requested:
                    self.live_dashboard_refresh_requested = False
                    rows = self.store.dashboard_record_rows()
                    player_stats = self.store.dashboard_player_stats()
                    maps = self._dashboard_maps_by_record_key()
                    writes = await asyncio.to_thread(
                        self.live_dashboard.publish_leaderboards,
                        rows,
                        maps,
                        player_stats,
                    )
                    if writes:
                        self.store.set_json(
                            "live_dashboard_leaderboard_hashes",
                            self.live_dashboard.leaderboard_hashes,
                        )
                        self.store.set_json(
                            "live_dashboard_profile_hashes",
                            self.live_dashboard.profile_hashes,
                        )
                        self.store.set_json(
                            "live_dashboard_map_catalog",
                            self.live_dashboard.map_catalog,
                        )
                        LOG.info("published %d live dashboard leaderboard(s)", writes)
                    next_leaderboards = now + 60.0
            except asyncio.CancelledError:
                raise
            except Exception:
                LOG.exception("unable to publish live racing dashboard")
            try:
                await asyncio.wait_for(self.stop_event.wait(), timeout=5.0)
            except TimeoutError:
                pass

    async def broadcast_block(
        self,
        lines: Iterable[object],
    ) -> None:
        lines = list(lines)
        styled = style_console_block(lines)
        if styled:
            await self.sink.send(
                f"CONSOLE_MESSAGE {readline_console_block(styled)}"
            )

    async def private(self, player: Player | str, message: str) -> None:
        target = player.target if isinstance(player, Player) else player
        if not target or any(ch.isspace() for ch in target):
            return
        styled = style_console_message(message)
        await self.sink.send(f"PLAYER_MESSAGE {target} {quote_console(styled)}")

    async def private_block(
        self,
        player: Player | str,
        lines: Iterable[object],
    ) -> None:
        lines = list(lines)
        target = player.target if isinstance(player, Player) else player
        if not target or any(ch.isspace() for ch in target):
            return
        styled = style_console_block(lines)
        if styled:
            await self.sink.send(
                f"PLAYER_MESSAGE {target} {quote_console_block(styled)}"
            )

    async def center_private(self, player: Player, message: str) -> None:
        if not player.target or any(ch.isspace() for ch in player.target):
            return
        styled = style_console_message(message)
        await self.sink.send(
            f"CENTER_PLAYER_MESSAGE {player.target} {quote_console(styled)}"
        )

    async def center_broadcast(self, message: object) -> None:
        await self.sink.send(padded_center_command(message))

    def _checkpoint_center_text(
        self,
        player: Player,
        prefix: str = COLOR_RESET,
    ) -> str:
        required = tuple(getattr(self.current, "checkpoint_ids", ()) or ())
        if not required:
            return ""
        collected = player.checkpoints_collected
        if player.pending_respawn_kind == "spawn":
            collected = set()
        elif (
            player.pending_respawn_kind == "checkpoint"
            and player.checkpoint_snapshot is not None
        ):
            collected = set(player.checkpoint_snapshot.checkpoints_collected)
        count = sum(checkpoint_id in collected for checkpoint_id in required)
        return f"{prefix}{CHECKPOINT_CENTER_GAP}{count}/{len(required)}"

    async def _show_checkpoint_progress(
        self,
        player: Player,
        prefix: str = COLOR_RESET,
    ) -> bool:
        if not player.target or any(ch.isspace() for ch in player.target):
            return False
        message = self._checkpoint_center_text(player, prefix)
        if not message:
            return False
        await self.sink.send(
            f"CENTER_PLAYER_MESSAGE {player.target} "
            f"{quote_console_exact(message)}"
        )
        return True

    def _checkpoint_color_reset_commands(self, player: Player) -> tuple[str, ...]:
        if (
            not getattr(self.current, "checkpoint_ids", ())
            or not player.target
            or any(ch.isspace() for ch in player.target)
        ):
            return ()
        return (f"RESET_CHECKPOINT_PLAYER_COLORS {player.target}",)

    async def _show_go(self, player: Player) -> None:
        """Show the padded release cue, then erase it one second later."""
        if not player.target or any(ch.isspace() for ch in player.target):
            return
        if not await self._show_checkpoint_progress(player, "GO!"):
            cue = f"     {COLOR_SUCCESS}GO!{COLOR_RESET}     "
            await self.sink.send(
                f"CENTER_PLAYER_MESSAGE {player.target} "
                f"{quote_console_exact(cue)}"
            )
        old_task = self.center_clear_tasks.pop(id(player), None)
        if old_task:
            old_task.cancel()
        generation = player.generation
        self.center_clear_tasks[id(player)] = asyncio.create_task(
            self._clear_go(player, generation)
        )

    async def _clear_go(self, player: Player, generation: int) -> None:
        try:
            await asyncio.sleep(float(self.config.get("go_message_seconds", 1.0)))
            if (
                generation == player.generation
                and player.connected
                and player.active
            ):
                if not await self._show_checkpoint_progress(player):
                    await self.center_private(player, "")
        except asyncio.CancelledError:
            raise
        finally:
            current = self.center_clear_tasks.get(id(player))
            if current is asyncio.current_task():
                self.center_clear_tasks.pop(id(player), None)

    def player_for(self, name: str, create: bool = False) -> Player | None:
        player = self.aliases.get(name.casefold()) or self.players.get(name.casefold())
        if not player and create:
            player = Player(name, name)
            self._start_mode_for(player)
            self.players[name.casefold()] = player
            self.aliases[name.casefold()] = player
        return player

    def register_alias(self, player: Player, name: str) -> None:
        if name:
            self.aliases[name.casefold()] = player

    def estimate_game_time(self) -> float | None:
        if self.last_game_time is None or self.last_game_monotonic is None:
            return None
        return self.last_game_time + max(0.0, time.monotonic() - self.last_game_monotonic)

    def _round_started_after_transition(self, payload: str) -> bool:
        """Identify a target-round event that arrived before CURRENT_MAP."""
        started = getattr(self, "transition_started_epoch", None)
        if started is None:
            return False
        try:
            event_time = datetime.datetime.strptime(
                payload[:19], "%Y-%m-%d %H:%M:%S"
            ).replace(tzinfo=datetime.timezone.utc).timestamp()
        except (TypeError, ValueError):
            return False
        # Ladderlog timestamps have one-second precision.
        return event_time >= math.floor(started)

    async def _handle_round_started(self, payload: str) -> None:
        round_was_active = self._round_is_active()
        if self.transitioning and not self.transition_map_confirmed:
            # CURRENT_MAP is emitted while the target grid is created, before
            # ROUND_STARTED. If that writer was disabled in an older config,
            # remember an event produced after this transition began and apply
            # it as soon as the explicit map probe confirms the target.
            if self._round_started_after_transition(payload):
                self.transition_round_started_pending = True
                LOG.info(
                    "deferring ROUND_STARTED until map confirmation: %s",
                    self.transition_target_key or "unknown",
                )
            else:
                LOG.info(
                    "ignoring stale ROUND_STARTED while waiting for map: %s",
                    self.transition_target_key or "unknown",
                )
            self.round_active = False
            return
        current_key = self.current.key if self.current else None
        if (
            not self.transitioning
            and current_key
            and getattr(self, "round_started_map_key", None) == current_key
        ):
            # Native Armagetron must never replay a controller-managed map.
            LOG.error("native server attempted to repeat active map: %s", current_key)
            self.round_active = False
            await self.activate_next_map("native repeated the active map")
            return
        self.round_active = True
        if current_key:
            self._set_round_started_map(current_key)
        if self.transitioning:
            # Count the play window from when the selected map is playable.
            self.round_started_epoch = time.time()
            self.deadline_epoch = (
                self.round_started_epoch + self._map_open_play_seconds()
            )
            self.store.set_json("deadline_epoch", self.deadline_epoch)
            self.store.set_json("round_started_epoch", self.round_started_epoch)
            self._complete_map_transition()
        if not round_was_active:
            self._begin_helpful_message_round()
        await self._restore_persistent_ghosts_for_round()
        for player in self.players.values():
            if (
                player.connected
                and player.active
                and player.alive
                and not player.pending_respawn
            ):
                self._begin_new_attempt(player, 0.0)
            elif (
                player.connected
                and player.active
                and player.respawn_enabled
                and not player.alive
                and not player.pending_respawn
                and not getattr(self, "respawns_paused", False)
                and id(player) not in self.respawn_tasks
            ):
                self._schedule_respawn(player, delay_seconds=0.1)
        displayed_during_intermission = False
        if self._display_task and self._display_task.done():
            with contextlib.suppress(asyncio.CancelledError, Exception):
                displayed_during_intermission = bool(self._display_task.result())
        if not displayed_during_intermission:
            if self._display_task:
                self._display_task.cancel()
            self._display_task = asyncio.create_task(
                self._delayed_round_display(
                    expected_map_key=self.current.key if self.current else None
                )
            )

    async def handle_line(self, raw_line: str) -> None:
        line = raw_line.rstrip("\r\n")
        if not line:
            return
        event = line.split(" ", 1)[0]
        payload = line[len(event):].lstrip()
        try:
            if event == "ENCODING":
                tokens = payload.split()
                if tokens:
                    self._apply_advertised_game_encoding(tokens[0])
            elif event == "GAME_TIME":
                tokens = payload.split()
                if tokens:
                    self.last_game_time = float(tokens[-1])
                    self.last_game_monotonic = time.monotonic()
            elif event == "CURRENT_MAP":
                await self._handle_current_map(payload)
            elif event == "PLAYER_ENTERED_GRID":
                player = await self._handle_player_arrival(payload, True)
                if player:
                    self._publish_dashboard_presence("join", player)
            elif event == "PLAYER_LEAVES_SPECTATORS":
                await self._handle_player_arrival(payload, True)
            elif event == "PLAYER_ENTERED_SPECTATOR":
                player = await self._handle_player_arrival(payload, False)
                if player:
                    self._publish_dashboard_presence("join", player)
            elif event == "PLAYER_JOINS_SPECTATORS":
                await self._handle_player_arrival(payload, False)
            elif event == "PLAYER_AI_ENTERED":
                self._handle_player_ai_entered(payload)
            elif event == "PLAYER_LEFT":
                parts = payload.split(maxsplit=1)
                player = self.player_for(parts[0]) if parts else None
                if player:
                    self._publish_dashboard_presence("leave", player)
                self._handle_player_left(payload)
                await self._resolve_votes_after_eligibility_change()
            elif event == "PLAYER_LOGIN":
                player = self._handle_player_login(payload)
                if player:
                    self._publish_player_audit("login", player)
                    await self._deliver_saved_player_messages(player)
                    selector = getattr(self, "ghost_preferences", {}).get(
                        player.identity_key
                    )
                    if selector:
                        await self._command_ghost(
                            player, selector, automatic=True, silent=True
                        )
            elif event == "PLAYER_LOGOUT":
                parts = payload.split()
                player = self.player_for(parts[0]) if parts else None
                previous_auth_name = player.auth_name if player else ""
                player = self._handle_player_logout(payload)
                if player:
                    self._publish_player_audit(
                        "logout",
                        player,
                        authName=previous_auth_name or "",
                        authenticated=bool(previous_auth_name),
                    )
            elif event == "PLAYER_RENAMED":
                parts = payload.split(maxsplit=1)
                player = self.player_for(parts[0]) if parts else None
                previous_name = (
                    player.display_name
                    if player else parts[0] if parts else ""
                )
                player = self._handle_player_renamed(payload)
                if player:
                    self._publish_player_audit(
                        "rename", player, previousName=previous_name
                    )
            elif event == "PLAYER_COLORED_NAME":
                self._handle_player_colored_name(payload)
            elif event == "CHAT":
                parts = payload.split(maxsplit=1)
                if len(parts) == 2:
                    player = self.player_for(parts[0])
                    if player and player.connected and not player.is_ai:
                        live_config = self.config.get("live_dashboard", {})
                        self._publish_dashboard_chat(
                            self.server_id,
                            str(live_config.get("local_region", "LOCAL"))[:16],
                            player.display_name,
                            parts[1],
                            bool(player.auth_name),
                        )
                        if not clean_console_text(parts[1]).startswith("/"):
                            self._publish_player_audit(
                                "chat",
                                player,
                                message=plain_console_text(parts[1]).strip()[:512],
                            )
            elif event == "PLAYER_ACTIVITY":
                await self._handle_player_activity_snapshot(payload)
            elif event == "ONLINE_PLAYER":
                self._handle_online_player(payload)
            elif event == "ONLINE_PLAYERS_ALIVE":
                self._handle_online_status(payload, True)
            elif event == "ONLINE_PLAYERS_DEAD":
                self._handle_online_status(payload, False)
            elif event == "NEW_ROUND":
                self.round_active = False
                if not self._round_is_active():
                    self._cancel_helpful_message()
                for player in self.players.values():
                    player.generation += 1
                    player.pending_respawn = False
                    player.alive = False
                    player.attempt_started_game = None
                    player.respawn_created_game = None
                    self._clear_checkpoint_run(player)
                if self._display_task:
                    self._display_task.cancel()
                expected_map_key = (
                    self.transition_target_key
                    if self.transitioning and self.transition_target_key
                    else self.current.key if self.current else None
                )
                self._display_task = asyncio.create_task(
                    self._delayed_round_display(
                        delay_seconds=float(
                            self.config.get(
                                "round_intermission_display_delay_seconds", 0.0
                            )
                        ),
                        allow_intermission=True,
                        expected_map_key=expected_map_key,
                    )
                )
            elif event == "ROUND_STARTED":
                await self._handle_round_started(payload)
            elif event in {"ROUND_FINISHED", "ROUND_ENDED", "SHUTDOWN"}:
                self.round_active = False
                if not self._round_is_active():
                    self._cancel_helpful_message()
            elif event == "CYCLE_CREATED":
                self._handle_cycle_created(payload)
            elif event == "CYCLE_RELEASED":
                await self._handle_cycle_released(payload)
            elif event == "CYCLE_DESTROYED":
                await self._handle_cycle_destroyed(payload)
            elif event == "CYCLE_REPLAY_BEGIN":
                self._handle_replay_begin(payload)
            elif event == "CYCLE_REPLAY_STATE":
                self._handle_replay_state(payload)
            elif event == "CYCLE_REPLAY_INPUT":
                await self._handle_replay_input(payload)
            elif event == "CYCLE_REPLAY_END":
                await self._handle_replay_end(payload)
            elif event == "CYCLE_REPLAY_SETTINGS":
                self._handle_replay_settings(payload)
            elif event == "CHECKPOINT_PLAYER_ENTER":
                await self._handle_checkpoint(payload)
            elif event == "WINZONE_PLAYER_ENTER":
                await self._handle_winzone(payload)
            elif event == "COMMAND":
                await self._handle_command(payload)
        except Exception:
            LOG.exception("error processing ladderlog event: %s", line)

    async def _handle_current_map(self, payload: str) -> None:
        parts = payload.split(maxsplit=2)
        if not parts:
            return
        if len(parts) >= 3:
            with contextlib.suppress(ValueError):
                self.current_size_factor = float(parts[0])
        spec = parts[-1]
        entry = self.repository.find_by_spec(spec)
        if not entry:
            LOG.warning("active map is unavailable to TronnerRacing: %s", spec)
            saved_key = self.store.get_json("current_key", None)
            saved_entry = self.repository.catalog.get(saved_key)
            if saved_entry and not self.restoring_saved_map:
                self.restoring_saved_map = True
                LOG.info("restoring saved map after server restart: %s", saved_key)
                await asyncio.to_thread(self.repository.cache_for_server, saved_entry)
                self._begin_map_transition(saved_entry.key)
                await self.sink.send(
                    f"SIZE_FACTOR {format_size_factor(float(self.config.get('default_size_factor', 0)))}",
                    f"MAP_FILE {quote_console(saved_entry.key)}",
                    "START_NEW_MATCH",
                    "KILL_ALL",
                    "GET_CURRENT_MAP",
                )
            return
        self.restoring_saved_map = False
        previous_key = self.current.key if self.current else None
        if self.transitioning:
            self.transition_observed_key = entry.key
            # A failed load can leave online_players.txt briefly naming the
            # requested map even after the game has fallen back. Every fresh
            # CURRENT_MAP response must therefore be able to revoke a stale
            # confirmation as well as grant one.
            self.transition_map_confirmed = self.transition_target_key == entry.key
        changed = self.current_spec != spec
        if previous_key and previous_key != entry.key:
            self._remember_previous_map(self.current)
        self.current = entry
        if previous_key and previous_key != entry.key:
            self._clear_ghost_selections()
        if getattr(self, "current_map_selection", {}).get("resourcePath") != entry.key:
            self.next_map_selection = self._selection_for_map(
                entry, queued_via="native"
            )
            self._set_current_map_selection(entry)
        self.current_spec = spec
        saved_key = self.store.get_json("current_key", None)
        if previous_key and previous_key != entry.key:
            self._set_round_started_map(None)
        if changed or self.deadline_epoch is None:
            if saved_key != entry.key or not self.deadline_epoch:
                self.round_started_epoch = None
                self.deadline_epoch = time.time() + self._map_open_play_seconds(entry)
            self.store.set_json("current_key", entry.key)
            self.store.set_json("deadline_epoch", self.deadline_epoch)
            self.store.set_json("round_started_epoch", self.round_started_epoch)
            self._clear_all_votes()
            self._reset_attempts()
        self._publish_dashboard_map_change(previous_key or "")
        LOG.info("active map: %s", entry.key)
        if not getattr(self, "final_countdown_active", False):
            self._ensure_final_countdown_route_model()
        if (
            self.transitioning
            and self.transition_map_confirmed
            and getattr(self, "transition_round_started_pending", False)
        ):
            LOG.info(
                "completing map transition from deferred ROUND_STARTED: %s",
                entry.key,
            )
            self.transition_round_started_pending = False
            await self._handle_round_started("")

    def _handle_player_entered(
        self,
        payload: str,
        active: bool,
        clear_center: bool = True,
    ) -> Player | None:
        parts = payload.split(maxsplit=2)
        if len(parts) < 2:
            return None
        log_name = parts[0]
        # Grid/spectator entry includes an address between the log and display
        # names; team-menu join/leave events contain only the two names.
        display_name = parts[2] if len(parts) > 2 else parts[1]
        player = self.player_for(log_name, create=True)
        assert player
        player.log_name = log_name
        player.display_name = display_name
        if len(parts) > 2:
            player.connection_address = clean_console_text(parts[1])[:128]
            player.ip_address = normalized_connection_ip(parts[1])
        player.connected = True
        player.forced_racing = False
        player.active = active
        # Native team-menu state is authoritative for scripted respawning.
        # Joining spectators opts the player out until a later grid/team entry
        # explicitly opts them back in.
        player.respawn_enabled = active
        player.is_ai = False
        self.online_snapshot_misses.pop(id(player), None)
        if not player.active:
            # Immediately stop the current respawn/freeze task and all of its
            # player-scoped output.
            player.alive = False
            # Spectators are already excluded from votes. Clear any racer AFK
            # state silently so entering or leaving spectate never produces an
            # AFK status announcement.
            player.afk = False
            player.last_turn_monotonic = None
            self.finalists.discard(id(player))
            self._cancel_player_freeze(player)
            if clear_center:
                # Erase a countdown number that was already delivered before
                # the spectator event canceled subsequent freeze updates.
                asyncio.create_task(self.center_private(player, ""))
            getattr(self, "extend_votes", set()).discard(player.identity_key)
            getattr(self, "skip_votes", set()).discard(player.identity_key)
            player.suspended_votes.clear()
        self.players[log_name.casefold()] = player
        self.register_alias(player, log_name)
        return player

    async def _handle_player_arrival(
        self,
        payload: str,
        active: bool,
        force_racing: bool = False,
    ) -> Player | None:
        player = self._handle_player_entered(payload, active)
        if not player:
            return None
        if force_racing:
            player.active = True
            player.respawn_enabled = True
            player.forced_racing = True
            player.start_mode = "countdown"

        # Keep a native spectator out of the scripted spawn lifecycle. Leaving
        # spectator mode or entering the grid marks the player active,
        # re-enables respawning, and schedules their first spawn immediately
        # through this same path.
        if player.active and player.last_turn_monotonic is None:
            # A newly eligible racer gets one timeout window in which to make
            # their first turn.
            player.last_turn_monotonic = time.monotonic()
        await self._resolve_votes_after_eligibility_change()
        selector = getattr(self, "ghost_preferences", {}).get(player.identity_key)
        if selector:
            await self._command_ghost(
                player, selector, automatic=True, silent=True
            )
        if (
            player.active
            and self.round_active
            and not self.transitioning
            and not self.final_countdown_active
            and not getattr(self, "respawns_paused", False)
            and not player.alive
            and not player.pending_respawn
            and id(player) not in self.respawn_tasks
        ):
            self._schedule_respawn(player, delay_seconds=0.0)
        return player

    def _handle_player_left(self, payload: str) -> None:
        parts = payload.split(maxsplit=2)
        if not parts:
            return
        player = self.player_for(parts[0])
        if player:
            if player.identity_key in getattr(self, "ghost_selections", {}):
                self.ghost_selections.pop(player.identity_key, None)
            self.online_snapshot_misses.pop(id(player), None)
            player.connected = False
            player.active = False
            player.forced_racing = False
            player.alive = False
            self.finalists.discard(id(player))
            self._cancel_player_freeze(player)
            self.command_windows.pop(id(player), None)
            self.command_warning_times.pop(id(player), None)
            getattr(self, "extend_votes", set()).discard(player.identity_key)
            getattr(self, "skip_votes", set()).discard(player.identity_key)
            player.suspended_votes.clear()
            player.afk = False
            player.last_turn_monotonic = None
            player.activity_snapshot_seen = False

    def _handle_player_login(self, payload: str) -> Player | None:
        parts = payload.split(maxsplit=1)
        if len(parts) < 2:
            return None
        player = self.player_for(parts[0], create=True)
        assert player
        previous_identity = player.identity_key
        player.auth_name = parts[1].strip()
        self._move_ghost_selection(previous_identity, player.identity_key)
        self.register_alias(player, player.auth_name)
        previous_start_mode = getattr(self, "start_preferences", {}).get(
            previous_identity,
            player.start_mode,
        )
        if player.identity_key not in getattr(self, "start_preferences", {}):
            self.start_preferences[player.identity_key] = previous_start_mode
            self._save_start_preferences()
        self._start_mode_for(player)
        spawn_preferences_changed = False
        for map_key, map_preferences in list(self.spawn_preferences.items()):
            if (
                isinstance(map_preferences, dict)
                and previous_identity in map_preferences
                and player.identity_key not in map_preferences
            ):
                map_preferences[player.identity_key] = map_preferences[
                    previous_identity
                ]
                spawn_preferences_changed = True
        if spawn_preferences_changed:
            self._save_spawn_preferences()
        if self.current:
            preferred = self._preferred_spawn_index(player)
            if preferred is not None:
                player.spawn_cursor = preferred
        return player

    def _handle_player_ai_entered(self, payload: str) -> None:
        parts = payload.split(maxsplit=1)
        if not parts:
            return
        player = self.player_for(parts[0], create=True)
        assert player
        player.is_ai = True
        player.connected = True
        self.online_snapshot_misses.pop(id(player), None)
        player.active = True
        if len(parts) > 1:
            player.display_name = parts[1]

    def _handle_player_logout(self, payload: str) -> Player | None:
        parts = payload.split()
        if not parts:
            return None
        player = self.player_for(parts[0])
        if player:
            previous_identity = player.identity_key
            player.auth_name = None
            selections = getattr(self, "ghost_selections", {})
            if previous_identity in selections:
                state = selections.pop(previous_identity)
                selections.setdefault(player.identity_key, state)
        return player

    def _handle_player_renamed(self, payload: str) -> Player | None:
        parts = payload.split(maxsplit=4)
        if len(parts) < 4:
            return None
        old_name, new_name = parts[0], parts[1]
        player = self.player_for(old_name, create=True)
        assert player
        self.players.pop(player.log_name.casefold(), None)
        player.log_name = new_name
        player.colored_name = None
        if parts[3] == "1":
            player.auth_name = new_name
        if len(parts) > 4:
            player.display_name = parts[4]
        self.players[new_name.casefold()] = player
        self.register_alias(player, old_name)
        self.register_alias(player, new_name)
        return player

    def _handle_player_colored_name(self, payload: str) -> None:
        parts = payload.split(maxsplit=1)
        if len(parts) < 2:
            return
        player = self.player_for(parts[0], create=True)
        assert player
        player.colored_name = normalize_console_colors(parts[1])
        self.register_alias(player, parts[0])

    def _handle_online_player(self, payload: str) -> None:
        parts = payload.split()
        if len(parts) < 7:
            return
        player = self.player_for(parts[0], create=True)
        assert player
        try:
            player.owner_id = int(parts[1])
        except ValueError:
            pass
        else:
            # Dedicated-server bots, including private replay ghosts, use
            # owner zero. ONLINE_PLAYER may arrive after PLAYER_AI_ENTERED,
            # so never reclassify such a server-owned player as human.
            player.is_ai = player.owner_id <= 0
        with contextlib.suppress(ValueError):
            red, green, blue = (
                max(0, min(15, int(value))) for value in parts[2:5]
            )
            player.color_code = (
                f"0x{red * 17:02x}{green * 17:02x}{blue * 17:02x}"
            )
        logged_in = parts[6] == "1"
        if logged_in:
            player.auth_name = parts[0]
        player.connected = True
        self.online_snapshot_misses.pop(id(player), None)
        # ONLINE_PLAYER includes a ping field for spectators; only the next
        # field is a native team. Script-forced racers intentionally have no
        # native team and remain active until they explicitly spectate.
        player.active = len(parts) >= 9 or player.forced_racing
        self.register_alias(player, parts[0])

    def _handle_online_status(self, payload: str, alive: bool) -> None:
        for name in payload.split():
            player = self.player_for(name)
            if not player:
                continue
            player.connected = True
            self.online_snapshot_misses.pop(id(player), None)
            player.alive = alive

    def _record_replay_route_progress(
        self,
        capture: ReplayCapture,
        position: tuple[float, float],
    ) -> None:
        """Remember the smallest route-field distance reached by this run."""
        current = getattr(self, "current", None)
        model = getattr(self, "final_countdown_route_model", None)
        if (
            current is None
            or model is None
            or current.key != capture.resource_key
            or current.key != getattr(self, "final_countdown_route_map_key", None)
        ):
            return
        try:
            route_distance = float(model.distance_at(position))
        except (TypeError, ValueError, OverflowError):
            return
        if not math.isfinite(route_distance) or route_distance < 0:
            return
        previous = capture.closest_winzone_distance
        if previous is None or route_distance < previous:
            capture.closest_winzone_distance = route_distance

    def _handle_replay_begin(self, payload: str) -> None:
        parts = payload.split()
        if len(parts) < 9 or not self.current:
            return
        token, player_name = parts[:2]
        player = self.player_for(player_name)
        if not player or player.is_ai or token in self.replay_captures:
            return
        try:
            game_time, x, y, xdir, ydir, speed = map(float, parts[2:8])
            turns = int(parts[8])
        except (TypeError, ValueError):
            return
        initial_distance = 0.0
        if len(parts) >= 11:
            with contextlib.suppress(ValueError):
                initial_distance = max(0.0, float(parts[10]))
        if not all(math.isfinite(value) for value in (game_time, x, y, xdir, ydir, speed)):
            return
        player.cycle_xdir = xdir
        player.cycle_ydir = ydir
        player.cycle_speed = max(0.0, speed)
        player.cycle_turns = max(0, min(65535, turns))
        self._record_practice_snapshot(
            player,
            game_time,
            x,
            y,
            xdir=xdir,
            ydir=ydir,
            speed=speed,
            turns=turns,
        )
        previous_token = self.active_replay_tokens.get(id(player))
        previous = self.replay_captures.get(previous_token or "")
        if previous is not None and previous.outcome == "death":
            previous.outcome = "replaced"
        map_identifier = self.current.map_id or self.current.rating_key
        revision_identifier = self.current.revision_id or self.current.key
        capture = ReplayCapture(
            token=token,
            player_log_name=player.log_name,
            identity_key=player.identity_key,
            username=player.record_name,
            authenticated=bool(player.auth_name),
            map_identifier=map_identifier,
            revision_identifier=revision_identifier,
            resource_key=self.current.key,
            started_at=time.time(),
            spawn_game_time=game_time,
            x=x,
            y=y,
            xdir=xdir,
            ydir=ydir,
            speed=max(0.0, speed),
            initial_turns=max(0, turns),
            initial_distance=initial_distance,
            latest_distance=initial_distance,
            size_factor=self.current_size_factor,
            start_mode=self._start_mode_for(player),
            checkpoint_spawn=player.pending_respawn_kind == "checkpoint",
            record_key=map_records_key(self.current),
            storage_path=self.current.storage_path,
            settings_identifier=(
                parts[9]
                if len(parts) >= 10
                else getattr(self, "active_replay_settings_identifier", None)
            ),
        )
        self.replay_captures[token] = capture
        self.active_replay_tokens[id(player)] = token
        self._record_replay_route_progress(capture, (x, y))

    @staticmethod
    def _decode_replay_setting_hex(value: str) -> bytes:
        if value == "-":
            return b""
        if len(value) > 2_000_000 or len(value) % 2:
            raise ValueError("invalid replay setting field length")
        return bytes.fromhex(value)

    def _handle_replay_settings(self, payload: str) -> None:
        parts = payload.split()
        if not parts:
            return
        kind = parts[0]
        assemblies = getattr(self, "replay_settings_assemblies", None)
        if assemblies is None:
            assemblies = self.replay_settings_assemblies = {}
        if kind == "BEGIN" and len(parts) == 4:
            identifier = parts[1]
            try:
                format_version = int(parts[2])
                expected_count = int(parts[3])
            except ValueError:
                return
            if (
                format_version != REPLAY_SETTINGS_FORMAT_VERSION
                or expected_count < 0
                or expected_count > 20_000
            ):
                LOG.warning("unsupported replay settings snapshot: %s", payload)
                return
            assemblies[identifier] = ReplaySettingsAssembly(
                format_version,
                expected_count,
            )
            return
        if kind == "ITEM" and len(parts) == 4:
            assembly = assemblies.get(parts[1])
            if assembly is None or len(assembly.items) >= assembly.expected_count:
                return
            try:
                item = (
                    self._decode_replay_setting_hex(parts[2]),
                    self._decode_replay_setting_hex(parts[3]),
                )
            except ValueError:
                LOG.warning("invalid replay settings item for %s", parts[1])
                assemblies.pop(parts[1], None)
                return
            assembly.items.append(item)
            return
        if kind == "END" and len(parts) == 3:
            identifier = parts[1]
            assembly = assemblies.pop(identifier, None)
            try:
                reported_count = int(parts[2])
            except ValueError:
                return
            if (
                assembly is None
                or reported_count != assembly.expected_count
                or len(assembly.items) != assembly.expected_count
            ):
                LOG.warning("incomplete replay settings snapshot %s", identifier)
                return
            try:
                self.store.add_replay_settings(
                    identifier,
                    assembly.format_version,
                    assembly.items,
                )
            except Exception:
                LOG.exception("unable to save replay settings %s", identifier)
            return
        if kind == "ACTIVE" and len(parts) == 3:
            identifier = parts[1]
            try:
                game_time = float(parts[2])
            except ValueError:
                return
            if not math.isfinite(game_time):
                return
            self.active_replay_settings_identifier = identifier
            for capture in self.replay_captures.values():
                capture.add_settings_transition(game_time, identifier)

    def _handle_replay_state(self, payload: str) -> None:
        parts = payload.split()
        if len(parts) < 9:
            return
        token, state_kind = parts[:2]
        capture = self.replay_captures.get(token)
        if capture is None:
            return
        try:
            game_time, x, y, xdir, ydir, speed = map(float, parts[2:8])
            turns = int(parts[8])
        except (TypeError, ValueError):
            return
        distance = None
        if len(parts) >= 10:
            with contextlib.suppress(ValueError):
                distance = max(0.0, float(parts[9]))
        capture.update_state(
            game_time,
            x,
            y,
            xdir,
            ydir,
            speed,
            turns,
            distance=distance,
            released=state_kind == "release",
        )
        self._record_replay_route_progress(capture, (x, y))
        player = self.player_for(capture.player_log_name)
        if player is None:
            return
        player.cycle_xdir = xdir
        player.cycle_ydir = ydir
        player.cycle_speed = max(0.0, speed)
        player.cycle_turns = max(0, min(65535, turns))
        if state_kind == "death":
            self._prepare_practice_respawn(
                player,
                game_time,
                x,
                y,
                xdir,
                ydir,
                speed=speed,
                turns=turns,
            )
        else:
            self._record_practice_snapshot(
                player,
                game_time,
                x,
                y,
                xdir=xdir,
                ydir=ydir,
                speed=speed,
                turns=turns,
            )

    async def _handle_replay_input(self, payload: str) -> None:
        parts = payload.split()
        if len(parts) < 3:
            return
        token = parts[0]
        capture = self.replay_captures.get(token)
        if capture is None:
            return
        try:
            game_time = float(parts[1])
        except ValueError:
            return
        action = parts[2]
        state = None
        if action in {"L", "R"} and len(parts) >= 9:
            try:
                x, y, xdir, ydir, speed = map(float, parts[3:8])
                turns = int(parts[8])
            except ValueError:
                return
            if (
                all(math.isfinite(value) for value in (x, y, xdir, ydir, speed))
                and xdir * xdir + ydir * ydir > 1e-12
                and speed > 1e-12
                and 0 <= turns <= 65535
            ):
                state = ReplayEventState(
                    x,
                    y,
                    xdir,
                    ydir,
                    speed,
                    turns,
                )
                self._record_replay_route_progress(capture, (x, y))
        added = (
            capture.add_input(game_time, action, state)
            if state is not None
            else capture.add_input(game_time, action)
        )
        if not added:
            return
        player = self.player_for(capture.player_log_name)
        if player and action in {"L", "R"}:
            self._observe_cycle_turn(player, action)
            await self._record_player_turn(player)
        if action not in {"L", "R"}:
            return
        if (
            not player
            or self.active_replay_tokens.get(id(player)) != token
            or not self._final_countdown_progress_guard_enabled()
            or not getattr(self, "final_countdown_active", False)
            or not getattr(self, "final_countdown_end_epoch", None)
            or id(player) not in getattr(self, "finalists", set())
            or not player.connected
            or not player.active
            or not player.alive
            or player.is_ai
        ):
            return
        state = self.final_countdown_progress_states.setdefault(
            id(player), PlayerProgressState()
        )
        if state.killed:
            return
        limit = max(
            1,
            int(
                self.config.get(
                    "final_countdown_progress_same_turn_limit", 15
                )
            ),
        )
        count, exhausted = state.observe_turn(action, limit)
        if not exhausted:
            return
        state.killed = True
        direction = "left" if action == "L" else "right"
        await self.private(
            player,
            "Your final-countdown run was ended after "
            f"{count} consecutive {direction} turns.",
        )
        await self.sink.send(f"KILL_SILENT {player.target}")
        LOG.warning(
            "countdown-progress-guard repeated-turn-removed map=%s player=%s "
            "direction=%s count=%d limit=%d",
            self.current.key if self.current else "",
            player.identity_key,
            direction,
            count,
            limit,
        )

    def _persist_replay_capture(
        self,
        capture: ReplayCapture,
        ended_at: float | None = None,
    ) -> bool:
        try:
            self.store.add_replay(capture, ended_at or time.time())
            if capture.outcome == "finish" and capture.authenticated:
                self.store.mark_replay_available(
                    capture.record_key or capture.resource_key,
                    capture.identity_key,
                )
        except Exception:
            LOG.exception("unable to save replay capture %s", capture.token)
            return False
        return True

    async def _handle_replay_end(self, payload: str) -> None:
        parts = payload.split()
        if len(parts) < 3:
            return
        token, player_name = parts[:2]
        capture = self.replay_captures.pop(token, None)
        if capture is None:
            return
        try:
            end_game_time = float(parts[2])
        except ValueError:
            end_game_time = capture.spawn_game_time
        capture.death_reason = " ".join(parts[3:]).strip()
        player = self.player_for(player_name)
        if player is not None:
            capture.update_identity(player)
            if self.active_replay_tokens.get(id(player)) == token:
                self.active_replay_tokens.pop(id(player), None)
        if capture.outcome == "death" and capture.death_reason == "KILL_ALL":
            capture.outcome = "round_end"
        ended_at = capture.started_at + max(
            0.0, end_game_time - capture.spawn_game_time
        )
        saved = self._persist_replay_capture(capture, ended_at)
        if saved and (
            capture.outcome == "finish"
            or (
                capture.outcome in {"death", "round_end"}
                and capture.closest_winzone_distance is not None
            )
        ):
            await self._refresh_ghost_selections(
                capture.record_key or capture.resource_key
            )

    def _mark_replay_finish(
        self,
        player: Player,
        seconds: float,
        turns: int | None,
        personal_best: bool,
    ) -> None:
        token = getattr(self, "active_replay_tokens", {}).get(id(player))
        capture = getattr(self, "replay_captures", {}).get(token or "")
        if capture is None:
            return
        capture.update_identity(player)
        capture.outcome = "finish"
        capture.finish_seconds = seconds
        capture.finish_turns = turns
        capture.personal_best = personal_best

    def _handle_cycle_created(self, payload: str) -> None:
        parts = payload.split()
        if len(parts) < 6:
            return
        player = self.player_for(parts[0], create=True)
        assert player
        player.practice_attempt_tainted = self._practice_active(player)
        was_active = player.active
        player.alive = True
        player.activity_snapshot_seen = False
        if self._practice_active(player):
            player.practice_samples.clear()
            player.practice_respawn_snapshot = None
            player.practice_finish_pending = False
        with contextlib.suppress(ValueError):
            position = (float(parts[1]), float(parts[2]))
            xdir, ydir = float(parts[3]), float(parts[4])
            player.cycle_xdir = xdir
            player.cycle_ydir = ydir
            player.cycle_speed = 0.0
            player.cycle_turns = 0
        if player.is_ai:
            player.active = True
            return
        if not was_active:
            # A RESPAWN_PLAYER already in the console pipe can race with native
            # spectator selection. Remove that late cycle without restarting
            # its countdown or reactivating the player.
            player.pending_respawn = False
            asyncio.create_task(self.sink.send(f"KILL_SILENT {player.target}"))
            return
        player.active = True
        if (
            getattr(self, "respawns_paused", False)
            or not player.respawn_enabled
            or (
                self.final_countdown_active
                and id(player) not in self.finalists
            )
        ):
            # A late join or a respawn command already in the console pipe must
            # not introduce a new racer after final-chance timing has begun.
            # The same guard keeps /spec effective across normal round starts.
            player.pending_respawn = False
            asyncio.create_task(self.sink.send(f"KILL_SILENT {player.target}"))
            return
        try:
            event_time = float(parts[-1])
        except ValueError:
            return
        if (
            player.checkpoint_respawn_requested
            and player.checkpoint_snapshot is not None
            and player.pending_respawn_kind != "checkpoint"
        ):
            # /cp can overtake an ordinary respawn already waiting in the
            # server's console pipe. Remove that stale spawn; its destruction
            # will schedule the requested checkpoint cycle.
            player.pending_respawn = False
            player.respawn_created_game = None
            asyncio.create_task(self.sink.send(f"KILL_SILENT {player.target}"))
            return
        respawn_kind = player.pending_respawn_kind
        starts_without_hold = player.pending_start_mode in {
            "immediate",
            "respawn",
        }
        if player.pending_respawn and starts_without_hold:
            if (
                respawn_kind != "checkpoint"
                or not self._resume_checkpoint_attempt(player, event_time)
            ):
                self._begin_new_attempt(player, event_time)
            player.pending_respawn = False
            player.respawn_created_game = None
            player.pending_respawn_kind = ""
        elif player.pending_respawn:
            player.respawn_created_game = event_time
        else:
            self._begin_new_attempt(player, event_time)
        if (
            respawn_kind != "checkpoint"
            and self.current
            and self.current.spawns
        ):
            try:
                x, y = float(parts[1]), float(parts[2])
                nearest = min(
                    range(len(self.current.spawns)),
                    key=lambda index: (self.current.spawns[index].x - x) ** 2
                    + (self.current.spawns[index].y - y) ** 2,
                )
                player.last_spawn_index = nearest
                if not player.pending_respawn:
                    preferred = self._preferred_spawn_index(player)
                    player.spawn_cursor = (
                        preferred
                        if preferred is not None
                        else (nearest + 1) % len(self.current.spawns)
                    )
            except ValueError:
                pass

    async def _handle_cycle_released(self, payload: str) -> None:
        parts = payload.split()
        if len(parts) < 2:
            return
        player = self.player_for(parts[0])
        if (
            not player
            or not player.pending_respawn
            or not player.connected
            or not player.active
            or not player.respawn_enabled
            or getattr(self, "respawns_paused", False)
            or (
                self.final_countdown_active
                and id(player) not in self.finalists
            )
            or self.transitioning
        ):
            return
        try:
            event_time = float(parts[-1])
        except ValueError:
            return
        respawn_kind = player.pending_respawn_kind
        if (
            respawn_kind != "checkpoint"
            or not self._resume_checkpoint_attempt(player, event_time)
        ):
            self._begin_new_attempt(player, event_time)
        player.pending_respawn = False
        player.respawn_created_game = None
        player.pending_respawn_kind = ""
        # Brake-start uses a persistent targeted center message. Explicitly
        # replace it with an empty one as soon as the held cycle is released.
        await self.center_private(player, "")
        if player.pending_start_mode == "countdown":
            await self._show_go(player)

    async def _handle_cycle_destroyed(self, payload: str) -> None:
        parts = payload.split()
        if not parts:
            return
        player = self.player_for(parts[0])
        if not player:
            return
        player.alive = False
        if player.is_ai:
            return
        if self._practice_active(player):
            if player.practice_start_respawn_pending:
                player.practice_samples.clear()
                player.practice_respawn_snapshot = None
            elif len(parts) >= 7:
                try:
                    x, y, xdir, ydir = map(float, parts[1:5])
                    death_game_time = float(parts[6])
                except ValueError:
                    pass
                else:
                    self._prepare_practice_respawn(
                        player,
                        death_game_time,
                        x,
                        y,
                        xdir,
                        ydir,
                    )
            player.practice_finish_pending = False
        held_cycle_destroyed = (
            player.pending_respawn and player.respawn_created_game is not None
        )
        if player.pending_respawn and not held_cycle_destroyed:
            # This is the old cycle disappearing after its replacement command
            # was queued; CYCLE_CREATED has not confirmed the held cycle yet.
            return
        player.checkpoints_collected.clear()
        player.checkpoint_notice_monotonic = None
        if held_cycle_destroyed:
            player.generation += 1
            player.pending_respawn = False
            player.respawn_created_game = None
            player.pending_respawn_kind = ""
            freeze_task = self.freeze_tasks.pop(id(player), None)
            if freeze_task:
                freeze_task.cancel()
        if (
            not self.round_active
            or self.transitioning
            or self.final_countdown_active
            or getattr(self, "respawns_paused", False)
            or not player.respawn_enabled
            or id(player) in self.respawn_tasks
        ):
            return
        if (
            self._start_mode_for(player) == "respawn"
            and not player.manual_restart_pending
        ):
            await self.center_private(player, "Type /restart to respawn")
            return
        self._schedule_respawn_after_death(
            player,
            empty_arena=not any(
                candidate.connected
                and candidate.active
                and candidate.alive
                for candidate in {id(item): item for item in self.players.values()}.values()
                if candidate is not player
            ),
        )

    def _schedule_respawn_after_death(
        self,
        player: Player,
        empty_arena: bool = False,
    ) -> None:
        if player.checkpoint_snapshot is not None:
            player.checkpoint_respawn_requested = True
            if player.checkpoint_respawn_speed is None:
                player.checkpoint_respawn_speed = player.checkpoint_snapshot.speed
        # The player's /start delay is authoritative for every death. Do not
        # change it based on whether another racer happens to be alive.
        del empty_arena
        self._start_mode_for(player)
        self._schedule_respawn(
            player,
            delay_seconds=player.start_respawn_delay_seconds,
        )

    def _schedule_respawn(
        self, player: Player, delay_seconds: float | None = None
    ) -> None:
        if getattr(self, "respawns_paused", False):
            return
        generation = player.generation
        old_task = self.respawn_tasks.pop(id(player), None)
        if old_task:
            old_task.cancel()
        self.respawn_tasks[id(player)] = asyncio.create_task(
            self._respawn_after_delay(player, generation, delay_seconds)
        )

    async def _respawn_after_delay(
        self,
        player: Player,
        generation: int,
        delay_seconds: float | None = None,
    ) -> None:
        try:
            await asyncio.sleep(
                max(
                    0.0,
                    float(
                        self.config.get("respawn_delay_seconds", 2.0)
                        if delay_seconds is None
                        else delay_seconds
                    ),
                )
            )
            if (
                generation != player.generation
                or not self.round_active
                or not player.connected
                or not player.active
                or player.alive
                or not player.respawn_enabled
                or self.final_countdown_active
                or self.transitioning
                or getattr(self, "respawns_paused", False)
            ):
                return
            await self._respawn_player(player)
        except asyncio.CancelledError:
            raise
        finally:
            current = self.respawn_tasks.get(id(player))
            if current is asyncio.current_task():
                self.respawn_tasks.pop(id(player), None)

    async def _respawn_player(self, player: Player) -> None:
        if (
            not self.current
            or not self.current.spawns
            or not player.connected
            or not player.active
            or not player.respawn_enabled
            or self.final_countdown_active
            or self.transitioning
            or getattr(self, "respawns_paused", False)
        ):
            return
        start_mode = self._start_mode_for(player)
        countdown_seconds = DEFAULT_START_COUNTDOWN_SECONDS
        manual_restart = player.manual_restart_pending
        if start_mode == "respawn" and not manual_restart:
            await self.center_private(player, "Type /restart to respawn")
            return
        player.manual_restart_pending = False
        practice_start_respawn = (
            self._practice_active(player)
            and player.practice_start_respawn_pending
        )
        player.practice_start_respawn_pending = False
        if practice_start_respawn:
            player.practice_respawn_snapshot = None
            player.practice_samples.clear()
        elif (
            self._practice_active(player)
            and player.practice_respawn_snapshot is not None
        ):
            await self._respawn_from_practice(player)
            return
        if player.checkpoint_respawn_requested:
            if player.checkpoint_snapshot is not None:
                await self._respawn_from_checkpoint(player)
                return
            player.checkpoint_respawn_requested = False
            player.checkpoint_respawn_speed = None
        preferred = self._preferred_spawn_index(player)
        spawn_index = (
            preferred
            if preferred is not None
            else player.spawn_cursor % len(self.current.spawns)
        )
        spawn = self.current.spawns[spawn_index]
        if preferred is None:
            player.spawn_cursor = (spawn_index + 1) % len(self.current.spawns)
        else:
            player.spawn_cursor = preferred
        player.generation += 1
        generation = player.generation
        player.pending_respawn = True
        player.respawn_created_game = None
        player.pending_respawn_kind = "spawn"
        player.attempt_started_game = None
        player.pending_start_mode = start_mode
        spawn_arguments = (
            f"{player.target} false {spawn.x:.9g} {spawn.y:.9g} "
            f"{spawn.xdir:.9g} {spawn.ydir:.9g}"
        )
        if start_mode in {"immediate", "respawn"}:
            await self.sink.send(
                *self._checkpoint_color_reset_commands(player),
                f"RESPAWN_PLAYER {spawn_arguments}",
            )
            return
        if start_mode == "countdown":
            await self.sink.send(
                *self._checkpoint_color_reset_commands(player),
                f"RESPAWN_PLAYER_BRAKED {spawn_arguments} {countdown_seconds}",
            )
        else:
            await self.sink.send(
                *self._checkpoint_color_reset_commands(player),
                f"RESPAWN_PLAYER_BRAKED {spawn_arguments}",
            )
        old_task = self.freeze_tasks.pop(id(player), None)
        if old_task:
            old_task.cancel()
        wait_for_start = (
            self._wait_for_countdown_start(
                player, generation, countdown_seconds
            )
            if start_mode == "countdown"
            else self._wait_for_brake_start(player, generation)
        )
        self.freeze_tasks[id(player)] = asyncio.create_task(
            wait_for_start
        )

    async def _respawn_from_checkpoint(self, player: Player) -> None:
        snapshot = player.checkpoint_snapshot
        if snapshot is None:
            player.checkpoint_respawn_requested = False
            player.checkpoint_respawn_speed = None
            return
        player.generation += 1
        generation = player.generation
        player.pending_respawn = True
        player.respawn_created_game = None
        player.pending_respawn_kind = "checkpoint"
        player.attempt_started_game = None
        start_mode = self._start_mode_for(player)
        countdown_seconds = DEFAULT_START_COUNTDOWN_SECONDS
        player.pending_start_mode = start_mode
        speed = (
            snapshot.speed
            if player.checkpoint_respawn_speed is None
            else player.checkpoint_respawn_speed
        )
        spawn_arguments = (
            f"{player.target} false {snapshot.x:.9g} {snapshot.y:.9g} "
            f"{snapshot.xdir:.9g} {snapshot.ydir:.9g} "
            f"{speed:.9g} {snapshot.turns}"
        )
        if start_mode == "immediate":
            await self.sink.send(
                f"RESPAWN_PLAYER_CHECKPOINT {spawn_arguments}",
            )
            return
        if start_mode == "countdown":
            await self.sink.send(
                "RESPAWN_PLAYER_CHECKPOINT_BRAKED "
                f"{spawn_arguments} {countdown_seconds}",
            )
        else:
            await self.sink.send(
                f"RESPAWN_PLAYER_CHECKPOINT_BRAKED {spawn_arguments}"
            )
        old_task = self.freeze_tasks.pop(id(player), None)
        if old_task:
            old_task.cancel()
        wait_for_start = (
            self._wait_for_countdown_start(
                player, generation, countdown_seconds
            )
            if start_mode == "countdown"
            else self._wait_for_brake_start(player, generation)
        )
        self.freeze_tasks[id(player)] = asyncio.create_task(
            wait_for_start
        )

    async def _respawn_from_practice(self, player: Player) -> None:
        snapshot = player.practice_respawn_snapshot
        if snapshot is None or not self._practice_active(player):
            return
        reset_commands = self._checkpoint_color_reset_commands(player)
        self._clear_checkpoint_run(player)
        player.practice_respawn_snapshot = None
        player.practice_samples.clear()
        player.generation += 1
        generation = player.generation
        player.pending_respawn = True
        player.respawn_created_game = None
        player.pending_respawn_kind = "practice"
        player.attempt_started_game = None
        start_mode = self._start_mode_for(player)
        countdown_seconds = DEFAULT_START_COUNTDOWN_SECONDS
        player.pending_start_mode = start_mode
        speed = snapshot.speed if player.practice_mode == "maintain" else 0.0
        zone_protection = bool(
            self.config.get(
                "practice_deathzone_protection_enabled", False
            )
        )
        respawn_command = (
            "RESPAWN_PLAYER_PRACTICE"
            if zone_protection
            else "RESPAWN_PLAYER_CHECKPOINT"
        )
        spawn_arguments = (
            f"{player.target} false {snapshot.x:.9g} {snapshot.y:.9g} "
            f"{snapshot.xdir:.9g} {snapshot.ydir:.9g} "
            f"{speed:.9g} {snapshot.turns}"
        )
        if start_mode in {"immediate", "respawn"}:
            await self.sink.send(
                *reset_commands,
                f"{respawn_command} {spawn_arguments}",
            )
            return
        braked_respawn_command = (
            "RESPAWN_PLAYER_PRACTICE_BRAKED"
            if zone_protection
            else "RESPAWN_PLAYER_CHECKPOINT_BRAKED"
        )
        if start_mode == "countdown":
            await self.sink.send(
                *reset_commands,
                f"{braked_respawn_command} {spawn_arguments} "
                f"{countdown_seconds}",
            )
        else:
            await self.sink.send(
                *reset_commands,
                f"{braked_respawn_command} {spawn_arguments}",
            )
        old_task = self.freeze_tasks.pop(id(player), None)
        if old_task:
            old_task.cancel()
        wait_for_start = (
            self._wait_for_countdown_start(
                player, generation, countdown_seconds
            )
            if start_mode == "countdown"
            else self._wait_for_brake_start(player, generation)
        )
        self.freeze_tasks[id(player)] = asyncio.create_task(wait_for_start)

    async def _wait_for_brake_start(self, player: Player, generation: int) -> None:
        try:
            await self.center_private(
                player,
                "Press brake to start",
            )
            while (
                generation == player.generation
                and player.connected
                and player.active
                and player.respawn_enabled
                and not self.final_countdown_active
                and not self.transitioning
                and not getattr(self, "respawns_paused", False)
                and player.pending_respawn
            ):
                await asyncio.sleep(0.1)
        except asyncio.CancelledError:
            raise
        finally:
            current = self.freeze_tasks.get(id(player))
            if current is asyncio.current_task():
                self.freeze_tasks.pop(id(player), None)

    async def _wait_for_countdown_start(
        self,
        player: Player,
        generation: int,
        countdown_seconds: int,
    ) -> None:
        try:
            for number in range(countdown_seconds, 0, -1):
                if not (
                    generation == player.generation
                    and player.connected
                    and player.active
                    and player.respawn_enabled
                    and not self.final_countdown_active
                    and not self.transitioning
                    and not getattr(self, "respawns_paused", False)
                    and player.pending_respawn
                    and player.pending_start_mode == "countdown"
                ):
                    return
                if not await self._show_checkpoint_progress(player, str(number)):
                    await self.center_private(player, str(number))
                await asyncio.sleep(1.0)
        except asyncio.CancelledError:
            raise
        finally:
            current = self.freeze_tasks.get(id(player))
            if current is asyncio.current_task():
                self.freeze_tasks.pop(id(player), None)

    def _missing_checkpoints(self, player: Player) -> tuple[int, ...]:
        required = tuple(getattr(self.current, "checkpoint_ids", ()) or ())
        return tuple(
            checkpoint_id
            for checkpoint_id in required
            if checkpoint_id not in player.checkpoints_collected
        )

    async def _checkpoint_notice(
        self,
        player: Player,
        message: str,
        *,
        throttle: bool = False,
    ) -> None:
        now = time.monotonic()
        if (
            throttle
            and player.checkpoint_notice_monotonic is not None
            and now - player.checkpoint_notice_monotonic < 1.5
        ):
            return
        player.checkpoint_notice_monotonic = now
        await self.private(player, message)

    async def _handle_checkpoint(self, payload: str) -> None:
        parsed = parse_checkpoint_entry(payload)
        required = tuple(getattr(self.current, "checkpoint_ids", ()) or ())
        if not parsed or not required:
            return
        checkpoint_id = parsed.checkpoint_id
        player = self.player_for(parsed.player_name)
        if (
            not player
            or player.is_ai
            or not player.alive
            or player.pending_respawn
            or player.attempt_started_game is None
        ):
            return
        if checkpoint_id not in required or checkpoint_id in player.checkpoints_collected:
            return
        mode = getattr(self.current, "checkpoint_mode", "ordered") or "ordered"
        if mode == "ordered":
            expected = next(
                item
                for item in required
                if item not in player.checkpoints_collected
            )
            if checkpoint_id != expected:
                await self._checkpoint_notice(
                    player,
                    f"Checkpoint {expected} must be collected next.",
                    throttle=True,
                )
                return
        player.checkpoints_collected.add(checkpoint_id)
        player.last_checkpoint_game = parsed.game_time
        segment_started = (
            player.no_cp_segment_started_game
            if player.no_cp_segment_started_game is not None
            else player.attempt_started_game
        )
        segment_seconds = parsed.game_time - segment_started
        if segment_seconds >= 0 and math.isfinite(segment_seconds):
            player.no_cp_elapsed += segment_seconds
            player.no_cp_segment_started_game = parsed.game_time
            if parsed.has_respawn_state:
                assert parsed.x is not None
                assert parsed.y is not None
                assert parsed.xdir is not None
                assert parsed.ydir is not None
                assert parsed.speed is not None
                assert parsed.turns is not None
                player.checkpoint_snapshot = CheckpointSnapshot(
                    checkpoint_id=checkpoint_id,
                    x=parsed.x,
                    y=parsed.y,
                    xdir=parsed.xdir,
                    ydir=parsed.ydir,
                    speed=parsed.speed,
                    turns=parsed.turns,
                    event_game=parsed.game_time,
                    attempt_started_game=player.attempt_started_game,
                    checkpoints_collected=frozenset(
                        player.checkpoints_collected
                    ),
                    no_cp_elapsed=player.no_cp_elapsed,
                )
        await self.sink.send(
            f"SET_CHECKPOINT_PLAYER_COLOR {player.target} {checkpoint_id}"
        )
        await self._show_checkpoint_progress(player)

    async def _handle_winzone(self, payload: str) -> None:
        parsed = parse_winzone_finish(payload)
        if not parsed or not self.current:
            return
        map_key = map_records_key(self.current)
        time_decimals = race_time_decimals(self.current)
        player_name, finish_game, turns = parsed
        player = self.player_for(player_name)
        if not player or player.is_ai or not player.alive:
            return
        if player.attempt_started_game is None:
            # Held brake/countdown cycles exist in the arena before takeoff.
            # A spawn inside the win zone therefore emits events before there
            # is a valid attempt to finish; ignore them instead of creating a
            # kill/respawn loop. Completed finishes mark the player dead below,
            # so their repeated zone ticks are already rejected above.
            return
        practice_finish = (
            self._practice_active(player)
            or player.practice_attempt_tainted
        )
        if practice_finish:
            if player.practice_finish_pending:
                return
            player.practice_finish_pending = True
            await self.private(
                player,
                "Practice finish reached; no time or score was recorded."
                if self._practice_active(player)
                else (
                    "This life used practice mode, so no time or score was "
                    "recorded. Your next life can record normally."
                ),
            )
            await self.sink.send(
                *self._checkpoint_color_reset_commands(player),
                f"KILL_SILENT {player.target}",
            )
            return
        missing_checkpoints = self._missing_checkpoints(player)
        if missing_checkpoints:
            mode = getattr(self.current, "checkpoint_mode", "ordered") or "ordered"
            required_count = len(getattr(self.current, "checkpoint_ids", ()))
            if mode == "ordered":
                message = (
                    f"Finish blocked: collect checkpoint {missing_checkpoints[0]} next "
                    f"({len(player.checkpoints_collected)}/{required_count})."
                )
            else:
                message = (
                    f"Finish blocked: {len(missing_checkpoints)} checkpoint"
                    f"{'s' if len(missing_checkpoints) != 1 else ''} remaining."
                )
            await self._checkpoint_notice(player, message, throttle=True)
            return
        attempt_started_game = player.attempt_started_game
        seconds = finish_game - attempt_started_game
        if seconds < 0 or seconds > float(self.config.get("maximum_record_seconds", 7200)):
            LOG.warning("discarding invalid finish %.6f for %s", seconds, player.record_name)
            token = getattr(self, "active_replay_tokens", {}).get(id(player))
            capture = getattr(self, "replay_captures", {}).get(token or "")
            if capture is not None:
                capture.outcome = "invalid_finish"
            player.attempt_started_game = None
            self._clear_checkpoint_run(player)
            player.alive = False
            await self.sink.send(
                *self._checkpoint_color_reset_commands(player),
                f"KILL_SILENT {player.target}",
            )
            return
        no_cp_seconds: float | None = None
        if (
            player.checkpoint_respawn_used
            and player.no_cp_segment_started_game is not None
        ):
            candidate = (
                player.no_cp_elapsed
                + finish_game
                - player.no_cp_segment_started_game
            )
            if 0 <= candidate <= float(
                self.config.get("maximum_record_seconds", 7200)
            ) and math.isfinite(candidate):
                no_cp_seconds = candidate
        self._clear_checkpoint_run(player)
        # Keep the final-countdown loop from advancing the map after this cycle
        # is marked dead but before its score, record, and message are complete.
        if not hasattr(self, "finishes_in_progress"):
            self.finishes_in_progress = set()
        self.finishes_in_progress.add(id(player))
        player.attempt_started_game = None
        player.alive = False
        try:
            # Native race scoring only recognizes a player's first finish in a
            # round. This controller permits repeated attempts, so score every
            # validated winzone entry here instead.
            await self.sink.send(
                *self._checkpoint_color_reset_commands(player),
                f"ADD_SCORE_PLAYER {player.target} 1",
            )
            record, improved, previous_best, previous_best_turns = (
                self.store.add_finish(map_key, player, seconds, turns)
            )
            self._mark_replay_finish(player, seconds, turns, improved)
            records = self.store.records(map_key)
            finish_key = (seconds, math.inf if turns is None else turns)
            finish_rank = 1 + sum(
                (
                    item.best_seconds,
                    math.inf if item.best_turns is None else item.best_turns,
                )
                < finish_key
                for item in records
            )
            best_rank = next(
                index
                for index, item in enumerate(records, 1)
                if item.identity_key == record.identity_key
            )
            previous_best_rank: int | None = None
            if improved and previous_best is not None:
                previous_key = (
                    previous_best,
                    math.inf
                    if previous_best_turns is None
                    else previous_best_turns,
                )
                previous_best_rank = 1 + sum(
                    (
                        item.best_seconds,
                        math.inf
                        if item.best_turns is None
                        else item.best_turns,
                    )
                    < previous_key
                    for item in records
                    if item.identity_key != record.identity_key
                )
            no_cp_rank: int | None = None
            if no_cp_seconds is not None:
                no_cp_key = (
                    no_cp_seconds,
                    math.inf if turns is None else turns,
                )
                no_cp_rank = 1 + sum(
                    (
                        item.best_seconds,
                        math.inf
                        if item.best_turns is None
                        else item.best_turns,
                    )
                    < no_cp_key
                    for item in records
                    if item.identity_key != record.identity_key
                )
            LOG.info(
                "finish map=%s username=%s time=%.*f personal_best=%s",
                map_key,
                player.record_name,
                time_decimals,
                seconds,
                improved,
            )
            self._publish_dashboard_finish_activity(
                player,
                seconds=seconds,
                rank=finish_rank,
                turns=turns,
                improved=improved,
                best_seconds=record.best_seconds,
                best_turns=record.best_turns,
                previous_best=previous_best,
                previous_best_turns=previous_best_turns,
                pb_rank=(previous_best_rank if improved else best_rank),
                no_cp_seconds=no_cp_seconds,
                no_cp_rank=no_cp_rank,
            )
            await self.result_message(
                format_finish_message(
                    player.colored_display_name,
                    seconds,
                    finish_rank,
                    record.best_seconds,
                    best_rank,
                    previous_best,
                    turns,
                    record.best_turns,
                    previous_best_turns,
                    no_cp_seconds,
                    no_cp_rank,
                    turns if no_cp_seconds is not None else None,
                    improved,
                    previous_best_rank,
                    time_decimals,
                ),
            )
        finally:
            self.finalists.discard(id(player))
            self.finishes_in_progress.discard(id(player))
            await self.sink.send(f"KILL_SILENT {player.target}")

    async def _delayed_round_display(
        self,
        delay_seconds: float | None = None,
        allow_intermission: bool = False,
        expected_map_key: str | None = None,
    ) -> bool:
        if delay_seconds is None:
            delay_seconds = float(
                self.config.get("round_display_delay_seconds", 0.35)
            )
        await asyncio.sleep(max(0.0, delay_seconds))
        if allow_intermission and delay_seconds <= 0:
            # NEW_ROUND arrives just before CURRENT_MAP during a map change.
            # A zero-delay table should appear at the earliest safe point: as
            # soon as the target map is confirmed, still before ROUND_STARTED.
            while (
                getattr(self, "transitioning", False)
                and not getattr(self, "transition_map_confirmed", False)
            ):
                await asyncio.sleep(0.01)
        if not self.current:
            return False
        if expected_map_key is not None and self.current.key != expected_map_key:
            return False
        if not self.round_active and not allow_intermission:
            return False
        if getattr(self, "transitioning", False) and not getattr(
            self, "transition_map_confirmed", False
        ):
            return False
        records = self.store.records(map_records_key(self.current))
        ranks = {record.identity_key: (index + 1, record) for index, record in enumerate(records)}
        delivered: set[str] = set()
        recipients: list[Player] = []
        personal_rows: list[
            tuple[str, int | str, str, float | None, int | None]
        ] = []
        for player in list(self.players.values()):
            if (
                player.is_ai
                or not player.connected
                or not player.active
                or player.identity_key in delivered
                or getattr(self, "result_message_preferences", {}).get(
                    player.identity_key, True
                ) is False
            ):
                continue
            delivered.add(player.identity_key)
            recipients.append(player)
            row = ranks.get(player.identity_key)
            if row:
                rank, record = row
                personal_rows.append(
                    (
                        player.identity_key,
                        rank,
                        record.username,
                        record.best_seconds,
                        record.best_turns,
                    )
                )
            else:
                personal_rows.append(
                    (player.identity_key, "--", player.record_name, None, None)
                )
        common_lines, private_lines = build_leaderboard_table(
            self._display_map_name(self.current),
            self.current.author,
            records,
            personal_rows,
            axes=self.current.axes,
            rating=self.store.rating_average(self.current.rating_key),
            time_decimals=race_time_decimals(self.current),
        )
        # Send each viewer one complete table so its rows cannot be reordered
        # with that viewer's personal-best row or the status footer.
        footer_lines = common_lines[-2:]
        map_minutes = self._map_play_seconds(self.current) / 60.0
        map_time_text = f"{map_minutes:.2f}".rstrip("0").rstrip(".")
        map_time_line = f"Map time: {map_time_text} minutes"
        for player in recipients:
            await self.private_block(
                player,
                [
                    *common_lines[:-2],
                    *private_lines.get(player.identity_key, []),
                    *footer_lines,
                    map_time_line,
                ],
            )

        return True

    def active_players(self) -> list[Player]:
        unique: dict[int, Player] = {}
        for player in self.players.values():
            if (
                player.connected
                and player.active
                and player.respawn_enabled
                and not player.is_ai
            ):
                unique[id(player)] = player
        return list(unique.values())

    def eligible_voters(self) -> list[Player]:
        """Return active network-owned human racers who count toward votes."""
        return [
            player
            for player in self.active_players()
            if not player.afk
            # Server-created players have owner zero. Keep this independent
            # of ladderlog event ordering so a replay ghost can never become
            # vote-eligible between its grid and AI classification events.
            and (player.owner_id is None or player.owner_id > 0)
        ]

    def _vote_generation(self, vote_name: str) -> int:
        return int(getattr(self, f"{vote_name}_vote_generation", 0))

    def _clear_vote(self, vote_name: str) -> None:
        votes_attribute = f"{vote_name}_votes"
        votes = getattr(self, votes_attribute, None)
        if votes is None:
            votes = set()
            setattr(self, votes_attribute, votes)
        votes.clear()
        setattr(
            self,
            f"{vote_name}_vote_generation",
            self._vote_generation(vote_name) + 1,
        )
        for player in {
            id(item): item for item in getattr(self, "players", {}).values()
        }.values():
            player.suspended_votes.pop(vote_name, None)

    def _clear_all_votes(self) -> None:
        self._clear_vote("extend")
        self._clear_vote("skip")

    def _suspend_player_votes(self, player: Player) -> bool:
        suspended = False
        identity_key = player.identity_key
        for vote_name in ("extend", "skip"):
            votes = getattr(self, f"{vote_name}_votes")
            if identity_key not in votes:
                continue
            votes.remove(identity_key)
            player.suspended_votes[vote_name] = self._vote_generation(vote_name)
            suspended = True
        return suspended

    def _restore_player_votes(self, player: Player) -> bool:
        if (
            not player.connected
            or not player.active
            or not player.respawn_enabled
            or player.is_ai
            or player.afk
            or not getattr(self, "current", None)
            or not self._round_is_active()
            or getattr(self, "transitioning", False)
        ):
            return False
        final_countdown_active = bool(
            getattr(self, "final_countdown_active", False)
        )
        restored = False
        for vote_name in ("extend", "skip"):
            if final_countdown_active and vote_name != "extend":
                continue
            generation = player.suspended_votes.pop(vote_name, None)
            if generation != self._vote_generation(vote_name):
                continue
            getattr(self, f"{vote_name}_votes").add(player.identity_key)
            restored = True
        return restored

    async def _resolve_extend_vote(self) -> bool:
        if not hasattr(self, "extend_votes"):
            self.extend_votes = set()
        if (
            not getattr(self, "current", None)
            or not self._round_is_active()
            or getattr(self, "transitioning", False)
        ):
            return False
        voters = self.eligible_voters()
        active_keys = {voter.identity_key for voter in voters}
        self.extend_votes.intersection_update(active_keys)
        required = (
            1
            if len(voters) <= 1
            else extend_votes_required(len(voters))
        )
        if not self.extend_votes or len(self.extend_votes) < required:
            return False
        extension = float(self.config.get("extend_seconds", 300))
        now = time.time()
        countdown_was_active = bool(
            getattr(self, "final_countdown_active", False)
        )
        self.deadline_epoch = max(now, self.deadline_epoch or now) + extension
        self.store.set_json("deadline_epoch", self.deadline_epoch)
        self._clear_vote("extend")
        if countdown_was_active:
            self._clear_final_countdown_state()
            # Replace the last global countdown number immediately. Dead
            # racers whose respawns were suppressed by the countdown can now
            # re-enter through the normal scripted lifecycle.
            await self.sink.send("CENTER_MESSAGE 0xffffff ")
            resumed = self._schedule_startup_respawns()
            await self.broadcast(
                "Extend vote passed. Final countdown cancelled; "
                "map extended by 5 minutes."
            )
            LOG.info(
                "final countdown cancelled by extend vote; resumed=%d deadline=%.3f",
                resumed,
                self.deadline_epoch,
            )
        else:
            await self.broadcast("Map extended by 5 minutes.")
        return True

    async def _resolve_skip_vote(self) -> bool:
        if not hasattr(self, "skip_votes"):
            self.skip_votes = set()
        if (
            not getattr(self, "current", None)
            or not self._round_is_active()
            or getattr(self, "transitioning", False)
            or getattr(self, "final_countdown_active", False)
            or getattr(self, "final_countdown_announcement", None)
        ):
            return False
        voters = self.eligible_voters()
        active_keys = {voter.identity_key for voter in voters}
        self.skip_votes.intersection_update(active_keys)
        required = 1 if len(voters) <= 1 else skip_votes_required(len(voters))
        if not self.skip_votes or len(self.skip_votes) < required:
            return False
        self._clear_vote("skip")
        # Mark the countdown active immediately so no respawn can slip in
        # before the map timer starts its countdown loop on the next tick.
        self.final_countdown_active = True
        self.final_countdown_end_epoch = None
        self.final_countdown_map_key = self.current.key
        self.final_countdown_announcement = "Skip vote passed."
        self.store.set_json("final_countdown_active", True)
        self.store.set_json("final_countdown_end_epoch", None)
        self.store.set_json("final_countdown_map_key", self.current.key)
        await self._disable_practice_for_countdown()
        idle_seconds = float(
            getattr(self, "config", {}).get("final_countdown_idle_seconds", 10)
        )
        if idle_seconds > 0 and not self._final_countdown_progress_guard_enabled():
            await self.sink.send(f"KILL_IDLE_PLAYERS {idle_seconds:.9g}")
        return True

    async def _resolve_votes_after_eligibility_change(self) -> None:
        # Resolve skip first during ordinary play. During a final countdown it
        # is intentionally ineligible, while an extend vote may cancel it.
        if await self._resolve_skip_vote():
            self._clear_vote("extend")
            return
        await self._resolve_extend_vote()

    async def _record_player_turn(
        self,
        player: Player,
        turn_time: float | None = None,
    ) -> None:
        player.last_turn_monotonic = (
            time.monotonic() if turn_time is None else turn_time
        )
        if not player.afk:
            return
        player.afk = False
        restored = self._restore_player_votes(player)
        if not player.active or not player.respawn_enabled:
            return
        await self.broadcast(
            f"{player.record_name} is no longer AFK."
            + (" Their active vote was restored." if restored else "")
        )
        await self._resolve_votes_after_eligibility_change()

    async def _set_player_afk(self, player: Player) -> None:
        if (
            player.afk
            or not player.connected
            or not player.active
            or not player.respawn_enabled
        ):
            return
        player.afk = True
        suspended = self._suspend_player_votes(player)
        await self.broadcast(
            f"{player.record_name} is now AFK and does not count toward votes."
            + (" Their vote is suspended." if suspended else "")
        )
        await self._resolve_votes_after_eligibility_change()

    async def _check_afk_players(self, now: float | None = None) -> None:
        now = time.monotonic() if now is None else now
        timeout = max(1.0, float(self.config.get("afk_timeout_seconds", 60)))
        players = {
            id(item): item for item in getattr(self, "players", {}).values()
        }.values()
        for player in players:
            if (
                player.connected
                and player.active
                and player.respawn_enabled
                and not player.is_ai
                and not player.afk
                and player.last_turn_monotonic is not None
                and now - player.last_turn_monotonic >= timeout
            ):
                await self._set_player_afk(player)

    async def _handle_player_activity_snapshot(self, payload: str) -> None:
        parts = payload.split()
        if len(parts) < 5:
            return
        player = self.player_for(parts[0])
        if not player or not player.connected or player.is_ai:
            return
        try:
            native_idle_seconds = max(0.0, float(parts[1]))
            cycle_alive = bool(int(parts[2]))
            position = (float(parts[3]), float(parts[4]))
        except ValueError:
            return
        snapshot_game_time = (
            self.estimate_game_time()
            if self._practice_active(player)
            else None
        )
        snapshot_direction: tuple[float, float] | None = None
        snapshot_speed: float | None = None
        snapshot_turns: int | None = None
        snapshot_distance: float | None = None
        last_turn_idle_seconds: float | None = None
        if len(parts) >= 10:
            try:
                exact_game_time = float(parts[5])
                exact_xdir = float(parts[6])
                exact_ydir = float(parts[7])
                exact_speed = float(parts[8])
                exact_turns = int(parts[9])
            except ValueError:
                return
            if (
                not all(
                    math.isfinite(value)
                    for value in (
                        exact_game_time,
                        exact_xdir,
                        exact_ydir,
                        exact_speed,
                    )
                )
                or exact_speed < 0
                or exact_turns < 0
                or exact_turns > 65535
            ):
                return
            snapshot_game_time = exact_game_time
            snapshot_direction = (exact_xdir, exact_ydir)
            snapshot_speed = exact_speed
            snapshot_turns = exact_turns
            if len(parts) >= 11:
                try:
                    exact_distance = float(parts[10])
                except ValueError:
                    return
                if not math.isfinite(exact_distance) or exact_distance < 0:
                    return
                snapshot_distance = exact_distance
            if len(parts) >= 12:
                try:
                    exact_turn_idle = float(parts[11])
                except ValueError:
                    return
                if not math.isfinite(exact_turn_idle) or exact_turn_idle < -1:
                    return
                if exact_turn_idle >= 0:
                    last_turn_idle_seconds = exact_turn_idle
        now = time.monotonic()
        player.activity_snapshot_seen = True

        if cycle_alive and last_turn_idle_seconds is not None:
            candidate_turn = now - last_turn_idle_seconds
            if (
                player.last_turn_monotonic is None
                or candidate_turn > player.last_turn_monotonic + 0.5
            ):
                await self._record_player_turn(player, candidate_turn)
        elif cycle_alive and player.last_turn_monotonic is None:
            # The engine has not observed a turn in this life. This normally
            # means the controller attached mid-run, so start one grace window
            # instead of marking the racer AFK immediately.
            player.last_turn_monotonic = now

        token = self.active_replay_tokens.get(id(player))
        capture = self.replay_captures.get(token or "")
        if capture is not None:
            if snapshot_distance is not None:
                capture.latest_distance = max(
                    capture.initial_distance, snapshot_distance
                )
            self._record_replay_route_progress(capture, position)

        if not cycle_alive:
            return

        if snapshot_game_time is not None:
            self._record_practice_snapshot(
                player,
                snapshot_game_time,
                position[0],
                position[1],
                xdir=(snapshot_direction[0] if snapshot_direction else None),
                ydir=(snapshot_direction[1] if snapshot_direction else None),
                speed=snapshot_speed,
                turns=snapshot_turns,
            )

        await self._record_final_countdown_progress(
            player, now, position, native_idle_seconds
        )

    def _final_countdown_progress_guard_enabled(self) -> bool:
        config = getattr(self, "config", {})
        return bool(
            config.get(
                "final_countdown_progress_guard_enabled",
                config.get("final_countdown_grief_detection_enabled", True),
            )
        )

    def _active_acceleration_capability(self) -> AccelerationCapability | None:
        identifier = getattr(self, "active_replay_settings_identifier", None)
        store = getattr(self, "store", None)
        if not identifier or store is None:
            return None
        try:
            settings_ref = store.replay_settings_ref(identifier)
            snapshot = (
                store.dashboard_replay_settings(settings_ref)
                if settings_ref is not None
                else None
            )
            rows = snapshot.get("settings", ()) if snapshot else ()
            settings = {
                str(row[0]): str(row[1])
                for row in rows
                if isinstance(row, (list, tuple)) and len(row) == 2
            }
        except (OSError, TypeError, ValueError, sqlite3.Error):
            LOG.exception("unable to read active cycle acceleration settings")
            return None
        return AccelerationCapability.from_settings(settings) if settings else None

    def _finish_final_countdown_route_build(self, map_key: str) -> None:
        if getattr(self, "final_countdown_route_map_key", None) == map_key:
            self.final_countdown_route_building = False

    def _schedule_final_countdown_guard(self, duration: float) -> None:
        self.final_countdown_progress_states = {}
        self.final_countdown_duration_seconds = max(1.0, float(duration))
        self._ensure_final_countdown_route_model()

    def _ensure_final_countdown_route_model(self) -> None:
        map_path = getattr(self.current, "local_path", None) if self.current else None
        if (
            not self._final_countdown_progress_guard_enabled()
            or not self.current
            or not map_path
        ):
            return
        map_key = self.current.key
        if (
            getattr(self, "final_countdown_route_map_key", None) == map_key
            and (
                getattr(self, "final_countdown_route_building", False)
                or getattr(self, "final_countdown_route_prepared", False)
            )
        ):
            return
        self.final_countdown_route_model = None
        self.final_countdown_route_map_key = map_key
        self.final_countdown_route_building = True
        self.final_countdown_route_prepared = False
        task = asyncio.create_task(
            self._prepare_final_countdown_guard(
                map_key=map_key,
                map_path=Path(map_path),
            ),
            name=f"final-countdown-route:{map_key}",
        )
        tasks = getattr(self, "final_countdown_route_tasks", None)
        if tasks is None:
            tasks = set()
            self.final_countdown_route_tasks = tasks
        tasks.add(task)
        def route_finished(completed: asyncio.Task) -> None:
            tasks.discard(completed)
            if completed.cancelled():
                self._finish_final_countdown_route_build(map_key)
                return
            error = completed.exception()
            if error is not None:
                self._finish_final_countdown_route_build(map_key)
                LOG.error(
                    "unexpected final-countdown route build failure map=%s",
                    map_key,
                    exc_info=(type(error), error, error.__traceback__),
                )
        task.add_done_callback(route_finished)

    async def _prepare_final_countdown_guard(
        self,
        *,
        map_key: str,
        map_path: Path,
    ) -> None:
        if (
            not self.current
            or self.current.key != map_key
            or self.final_countdown_route_map_key != map_key
        ):
            self._finish_final_countdown_route_build(map_key)
            return
        maximum_cells = min(
            500_000,
            max(
                1_000,
                int(
                    self.config.get(
                        "final_countdown_route_maximum_cells", 250_000
                    )
                ),
            ),
        )
        minimum_cell_size = max(
            0.1,
            float(self.config.get("final_countdown_route_minimum_cell_size", 0.5)),
        )
        wall_clearance = max(
            0.0,
            float(
                self.config.get(
                    "final_countdown_route_wall_clearance_cells", 0.0
                )
            ),
        )
        size_multiplier = 2.0 ** (
            float(getattr(self, "current_size_factor", 0.0) or 0.0) / 2.0
        )
        cache_value = str(
            self.config.get(
                "final_countdown_route_cache_dir",
                "/var/lib/tronner-racing/route-fields",
            )
        ).strip()
        cache_directory = Path(cache_value) if cache_value else None
        cache_maximum_entries = max(
            1,
            int(
                self.config.get(
                    "final_countdown_route_cache_maximum_entries", 768
                )
            ),
        )
        cache_maximum_bytes = max(
            1024 * 1024,
            int(
                self.config.get(
                    "final_countdown_route_cache_maximum_bytes",
                    512 * 1024 * 1024,
                )
            ),
        )
        self.final_countdown_route_building = True
        try:
            model, primary_cache_hit = await asyncio.to_thread(
                load_or_build_route_model,
                Path(map_path),
                cache_directory=cache_directory,
                cache_maximum_entries=cache_maximum_entries,
                cache_maximum_bytes=cache_maximum_bytes,
                maximum_cells=maximum_cells,
                minimum_cell_size=minimum_cell_size,
                wall_clearance_cells=wall_clearance,
                size_multiplier=size_multiplier,
                narrow_passage_guides=True,
            )
        except asyncio.CancelledError:
            self._finish_final_countdown_route_build(map_key)
            raise
        except (OSError, ET.ParseError, TypeError, ValueError):
            self._finish_final_countdown_route_build(map_key)
            LOG.exception(
                "unable to build final-countdown route model map=%s", map_key
            )
            return
        if primary_cache_hit:
            LOG.info("loaded final-countdown route model from cache map=%s", map_key)
        if (
            not self.current
            or self.current.key != map_key
            or self.final_countdown_route_map_key != map_key
        ):
            self._finish_final_countdown_route_build(map_key)
            return
        if model is not None and model.reference_distance <= 0:
            retry_maximum_cells = min(
                500_000,
                max(
                    maximum_cells,
                    int(
                        self.config.get(
                            "final_countdown_route_retry_maximum_cells", 500_000
                        )
                    ),
                ),
            )
            retry_minimum_cell_size = min(
                minimum_cell_size,
                max(
                    0.1,
                    float(
                        self.config.get(
                            "final_countdown_route_retry_minimum_cell_size", 0.1
                        )
                    ),
                ),
            )
            if (
                retry_maximum_cells > maximum_cells
                or retry_minimum_cell_size < minimum_cell_size
            ):
                LOG.info(
                    "retrying final-countdown route model at higher resolution "
                    "map=%s",
                    map_key,
                )
                try:
                    model, retry_cache_hit = await asyncio.to_thread(
                        load_or_build_route_model,
                        Path(map_path),
                        cache_directory=cache_directory,
                        cache_maximum_entries=cache_maximum_entries,
                        cache_maximum_bytes=cache_maximum_bytes,
                        maximum_cells=retry_maximum_cells,
                        minimum_cell_size=retry_minimum_cell_size,
                        wall_clearance_cells=wall_clearance,
                        size_multiplier=size_multiplier,
                        narrow_passage_guides=True,
                    )
                except asyncio.CancelledError:
                    self._finish_final_countdown_route_build(map_key)
                    raise
                except (OSError, ET.ParseError, TypeError, ValueError):
                    LOG.exception(
                        "unable to retry final-countdown route model map=%s",
                        map_key,
                    )
                    model = None
                else:
                    if retry_cache_hit:
                        LOG.info(
                            "loaded high-resolution final-countdown route model "
                            "from cache map=%s",
                            map_key,
                        )
        self._finish_final_countdown_route_build(map_key)
        if self.final_countdown_route_map_key != map_key:
            return
        if model is not None and model.reference_distance <= 0:
            model = None
        self.final_countdown_route_model = model
        self.final_countdown_route_prepared = True
        if model is None:
            LOG.warning(
                "final-countdown route model unavailable map=%s; using idle fallback",
                map_key,
            )
            return
        LOG.info(
            "final-countdown route model map=%s grid=%dx%d cell=%.3f "
            "reference_distance=%.3f teleports=%d subcell_guides=%d",
            map_key,
            model.width,
            model.height,
            model.cell_size,
            model.reference_distance,
            len(model.geometry.teleports),
            len(model.guide_points),
        )

    async def _record_final_countdown_progress(
        self,
        player: Player,
        now: float,
        position: tuple[float, float],
        native_idle_seconds: float = 0.0,
    ) -> None:
        model = getattr(self, "final_countdown_route_model", None)
        if (
            not self._final_countdown_progress_guard_enabled()
            or not getattr(self, "final_countdown_active", False)
            or not getattr(self, "final_countdown_end_epoch", None)
            or not self.current
            or self.current.key
            != getattr(self, "final_countdown_route_map_key", None)
            or id(player) not in getattr(self, "finalists", set())
            or not player.connected
            or not player.active
            or not player.alive
            or player.is_ai
        ):
            return
        state = getattr(self, "final_countdown_progress_states", {}).setdefault(
            id(player), PlayerProgressState()
        )
        if state.killed:
            return
        first_progress_sample = state.last_position_sample is None
        stationary_limit = max(
            0.1,
            float(
                self.config.get(
                    "final_countdown_progress_stationary_limit_seconds", 5.0
                )
            ),
        )
        stationary_warning_delay = max(
            0.0,
            float(
                self.config.get(
                    "final_countdown_progress_stationary_warning_delay_seconds",
                    1.0,
                )
            ),
        )
        stationary_update = state.observe_position(
            now,
            position,
            limit_seconds=stationary_limit,
            warning_delay_seconds=stationary_warning_delay,
            position_epsilon=max(
                0.0,
                float(
                    self.config.get(
                        "final_countdown_progress_stationary_position_epsilon",
                        self.config.get("afk_position_epsilon", 0.01),
                    )
                ),
            ),
            maximum_sample_gap_seconds=max(
                0.1,
                float(
                    self.config.get(
                        "final_countdown_progress_max_sample_gap_seconds", 2.0
                    )
                ),
            ),
        )
        if first_progress_sample:
            LOG.info(
                "countdown-progress-guard tracking map=%s player=%s route=%s",
                self.current.key,
                player.identity_key,
                (
                    "ready"
                    if model is not None
                    else "building"
                    if getattr(self, "final_countdown_route_building", False)
                    else "idle-fallback"
                ),
            )
        if stationary_update.warning_due:
            stationary_remaining = max(
                0.0, stationary_limit - stationary_update.stationary_seconds
            )
            await self.private(
                player,
                "Countdown progress warning: your cycle is stationary. "
                f"Move toward the winzone within {stationary_remaining:.1f} seconds.",
            )
            LOG.info(
                "countdown-progress-guard stationary-warning map=%s player=%s "
                "stationary=%.3f limit=%.3f",
                self.current.key,
                player.identity_key,
                stationary_update.stationary_seconds,
                stationary_limit,
            )
        if stationary_update.exhausted:
            state.killed = True
            await self.private(
                player,
                "Your final-countdown run was ended because your cycle remained "
                f"stationary for {stationary_limit:.1f} seconds.",
            )
            await self.sink.send(f"KILL_SILENT {player.target}")
            LOG.warning(
                "countdown-progress-guard stationary-removed map=%s player=%s "
                "stationary=%.3f limit=%.3f",
                self.current.key,
                player.identity_key,
                stationary_update.stationary_seconds,
                stationary_limit,
            )
            return
        required_checkpoints = set(getattr(self.current, "checkpoint_ids", ()))
        if required_checkpoints.difference(player.checkpoints_collected):
            # The current field targets the winzone.  Until a checkpoint-aware
            # field is available, do not mistake a required checkpoint detour
            # for wrong-way travel on maps that use the newer checkpoint mode.
            state.pending_positions.clear()
            state.clear_route_baseline()
            await self._record_final_countdown_idle_fallback(
                player, now, position, native_idle_seconds
            )
            return
        if model is None:
            if getattr(self, "final_countdown_route_building", False):
                state.pending_positions.append((now, position[0], position[1]))
                history_seconds = max(
                    10.0,
                    float(
                        getattr(
                            self, "final_countdown_duration_seconds", 0.0
                        )
                        or 0.0
                    ),
                )
                while (
                    state.pending_positions
                    and now - state.pending_positions[0][0] > history_seconds
                ):
                    state.pending_positions.popleft()
                return
            state.pending_positions.clear()
            state.clear_route_baseline()
            await self._record_final_countdown_idle_fallback(
                player, now, position, native_idle_seconds
            )
            return
        state.samples.clear()
        state.travel_distance = 0.0
        state.clear_violation()
        pending = list(state.pending_positions)
        state.pending_positions.clear()
        if not pending or abs(pending[-1][0] - now) > 1e-9:
            pending.append((now, position[0], position[1]))

        allowance = max(
            0.1,
            float(
                self.config.get(
                    "final_countdown_progress_wrong_way_allowance_seconds", 5.0
                )
            ),
        )
        warning_delay = max(
            0.0,
            float(
                self.config.get(
                    "final_countdown_progress_warning_delay_seconds", 1.0
                )
            ),
        )
        direction_slack = max(
            model.cell_size * 0.35,
            float(
                self.config.get(
                    "final_countdown_progress_direction_slack_distance",
                    self.config.get(
                        "final_countdown_grief_route_slack_distance", 0.25
                    ),
                )
            ),
        )
        maximum_sample_gap = max(
            0.1,
            float(
                self.config.get(
                    "final_countdown_progress_max_sample_gap_seconds", 2.0
                )
            ),
        )
        latest_update = None
        warnings_due = 0
        current_route_distance = math.inf
        winzone_margin = max(model.cell_size * 1.5, 0.5)
        for sample_time, sample_x, sample_y in pending:
            route_distance = model.distance_at((sample_x, sample_y))
            if sample_time == pending[-1][0]:
                current_route_distance = route_distance
            if not math.isfinite(route_distance):
                # Never bridge an unmodelled interval with a guessed straight
                # line. Preserve the already-used allowance and wait for two
                # consecutive route-aware samples.
                state.clear_route_baseline()
                latest_update = None
                continue
            if route_distance <= winzone_margin:
                state.last_route_sample = (sample_time, route_distance)
                state.clear_wrong_way_episode()
                latest_update = None
                continue
            latest_update = state.observe_route_distance(
                sample_time,
                route_distance,
                allowance_seconds=allowance,
                warning_delay_seconds=warning_delay,
                direction_slack_distance=direction_slack,
                maximum_sample_gap_seconds=maximum_sample_gap,
            )
            if latest_update.warning_due:
                warnings_due += 1

        if not math.isfinite(current_route_distance):
            await self._record_final_countdown_idle_fallback(
                player, now, position, native_idle_seconds
            )
            return
        if latest_update is None:
            return
        if warnings_due:
            await self.private(
                player,
                "Countdown progress warning: you are heading away from the "
                f"winzone. You have {latest_update.remaining_allowance_seconds:.1f} "
                f"of {allowance:.1f} wrong-way seconds left.",
            )
            LOG.info(
                "countdown-progress-guard warning map=%s player=%s "
                "wrong_way=%.3f allowance=%.3f remaining=%.3f route=%.3f",
                self.current.key if self.current else "",
                player.identity_key,
                latest_update.total_wrong_way_seconds,
                allowance,
                latest_update.remaining_allowance_seconds,
                current_route_distance,
            )
        if not latest_update.exhausted:
            return

        state.killed = True
        await self.private(
            player,
            "Your final-countdown run was ended after you used all "
            f"{allowance:.1f} seconds of your wrong-way allowance.",
        )
        await self.sink.send(f"KILL_SILENT {player.target}")
        LOG.warning(
            "countdown-progress-guard removed map=%s player=%s "
            "wrong_way=%.3f allowance=%.3f route=%.3f",
            self.current.key if self.current else "",
            player.identity_key,
            latest_update.total_wrong_way_seconds,
            allowance,
            current_route_distance,
        )

    async def _record_final_countdown_idle_fallback(
        self,
        player: Player,
        now: float,
        position: tuple[float, float],
        native_idle_seconds: float,
    ) -> None:
        idle_seconds = max(
            0.0, float(self.config.get("final_countdown_idle_seconds", 10))
        )
        if idle_seconds <= 0:
            return
        state = self.final_countdown_progress_states.setdefault(
            id(player), PlayerProgressState()
        )
        if state.killed:
            return
        if state.samples:
            state.travel_distance += math.dist(
                (state.samples[-1][1], state.samples[-1][2]),
                position,
            )
        state.samples.append(
            (now, position[0], position[1], 0.0, state.travel_distance)
        )
        while state.samples and now - state.samples[0][0] > idle_seconds * 1.2:
            state.samples.popleft()
        duration = (
            state.samples[-1][0] - state.samples[0][0]
            if len(state.samples) >= 2
            else 0.0
        )
        distance = sum(
            math.hypot(current[1] - previous[1], current[2] - previous[2])
            for previous, current in zip(state.samples, tuple(state.samples)[1:])
        )
        position_epsilon = max(
            0.0, float(self.config.get("afk_position_epsilon", 0.01))
        )
        stationary = (
            duration >= idle_seconds * 0.9
            and distance <= position_epsilon * max(1, len(state.samples) - 1)
        )
        idle = native_idle_seconds >= idle_seconds or stationary
        if not idle:
            state.clear_violation()
            return

        remaining = max(
            0.0, float(self.final_countdown_end_epoch) - time.time()
        )
        total = max(
            remaining,
            float(getattr(self, "final_countdown_duration_seconds", 0.0) or 0.0),
            1.0,
        )
        elapsed_fraction = min(1.0, max(0.0, 1.0 - remaining / total))
        early_grace = max(
            1.0,
            float(self.config.get("final_countdown_grief_early_grace_seconds", 6.0)),
        )
        late_grace = max(
            1.0,
            float(self.config.get("final_countdown_grief_late_grace_seconds", 2.0)),
        )
        grace = early_grace + (late_grace - early_grace) * elapsed_fraction
        state.last_reason = "idle on a map without a safe route model"
        if state.violation_started_at is None:
            state.violation_started_at = now
        if state.warned_at is None:
            state.warned_at = now
            await self.private(
                player,
                "Final countdown warning: provide input and keep moving toward "
                f"the finish. Your run will be ended if you remain idle for "
                f"{math.ceil(grace)} more seconds.",
            )
            return
        if now - state.warned_at < grace:
            return
        state.killed = True
        await self.private(
            player,
            "Your final-countdown run was ended because you remained idle "
            "after being warned.",
        )
        await self.sink.send(f"KILL_SILENT {player.target}")
        LOG.warning(
            "final-countdown idle fallback removed map=%s player=%s "
            "remaining=%.3f",
            self.current.key if self.current else "",
            player.identity_key,
            remaining,
        )

    async def player_activity_monitor(self) -> None:
        interval = max(
            0.25,
            float(self.config.get("afk_poll_interval_seconds", 1.0)),
        )
        last_final_countdown_idle_check = 0.0
        while True:
            now = time.monotonic()
            probe_settle_seconds = 0.0
            players = {
                id(item): item
                for item in getattr(self, "players", {}).values()
                if item.connected
                and item.active
                and item.alive
                and (
                    item.respawn_enabled
                    or id(item) in getattr(self, "finalists", set())
                )
                and not item.is_ai
            }.values()
            timeout = max(
                1.0,
                float(self.config.get("afk_timeout_seconds", 60)),
            )
            probe_lead = min(
                timeout,
                max(
                    1.0,
                    float(self.config.get("afk_probe_lead_seconds", 10)),
                ),
            )
            needs_baseline = any(
                not player.activity_snapshot_seen for player in players
            )
            at_risk = any(
                not player.afk
                and (
                    player.last_turn_monotonic is None
                    or now - player.last_turn_monotonic >= timeout - probe_lead
                )
                for player in players
            )
            recovering_afk = any(player.afk for player in players)
            final_countdown_racers = any(
                getattr(self, "final_countdown_active", False)
                and getattr(self, "final_countdown_end_epoch", None)
                and id(player) in getattr(self, "finalists", set())
                for player in players
            )
            practice_racers = any(
                self._practice_active(player) for player in players
            )
            practice_probe_interval = max(
                0.25,
                float(
                    self.config.get(
                        "practice_probe_interval_seconds", 0.25
                    )
                ),
            )
            loop_interval = (
                min(interval, practice_probe_interval)
                if practice_racers
                else interval
            )
            fallback_idle_seconds = float(
                self.config.get("final_countdown_idle_seconds", 10)
            )
            if (
                getattr(self, "final_countdown_active", False)
                and getattr(self, "final_countdown_end_epoch", None)
                and not self._final_countdown_progress_guard_enabled()
                and fallback_idle_seconds > 0
                and now - last_final_countdown_idle_check >= 1.0
            ):
                await self.sink.send(
                    f"KILL_IDLE_PLAYERS {fallback_idle_seconds:.9g}"
                )
                last_final_countdown_idle_check = now
            elif not getattr(self, "final_countdown_active", False):
                last_final_countdown_idle_check = 0.0
            should_probe = (
                now >= self.next_activity_probe_monotonic
                and (
                    needs_baseline
                    or at_risk
                    or recovering_afk
                    or final_countdown_racers
                    or practice_racers
                )
            )
            if should_probe:
                await self.sink.send("GET_PLAYER_ACTIVITY")
                normal_probe_interval = max(
                    1.0,
                    float(self.config.get("afk_probe_interval_seconds", 5)),
                )
                probe_interval = (
                    practice_probe_interval
                    if practice_racers
                    else max(
                        0.5,
                        float(
                            self.config.get(
                                "final_countdown_progress_probe_interval_seconds",
                                self.config.get(
                                    "final_countdown_grief_probe_interval_seconds",
                                    1.0,
                                ),
                            )
                        ),
                    )
                    if final_countdown_racers
                    else normal_probe_interval
                )
                self.next_activity_probe_monotonic = now + probe_interval
                # Let the ladderlog consumer apply the requested snapshot
                # before evaluating the AFK threshold.
                probe_settle_seconds = min(0.2, loop_interval / 2)
                await asyncio.sleep(probe_settle_seconds)
            await self._check_afk_players()
            await asyncio.sleep(
                max(0.01, loop_interval - probe_settle_seconds)
            )

    def _alive_finalists(self) -> list[Player]:
        unique: dict[int, Player] = {}
        for player in self.players.values():
            if (
                id(player) in self.finalists
                and (
                    id(player) in getattr(self, "finishes_in_progress", set())
                    or (player.connected and player.active and player.alive)
                )
            ):
                unique[id(player)] = player
        return list(unique.values())

    def _clock_runout_players(self, records: Sequence[Record]) -> list[Player]:
        if not self.config.get("clock_runout_prevention_enabled", True):
            return []
        if self.last_game_time is None:
            return []
        by_identity = {record.identity_key: record for record in records}
        minimum = max(
            0.0,
            float(self.config.get("clock_runout_minimum_seconds", 60)),
        )
        multiplier = max(
            1.0,
            float(self.config.get("clock_runout_personal_best_multiplier", 3)),
        )
        checkpoint_grace = max(
            0.0,
            float(self.config.get("clock_runout_checkpoint_grace_seconds", 20)),
        )
        candidates: list[Player] = []
        for player in self.active_players():
            record = by_identity.get(player.identity_key)
            if (
                record is None
                or not player.alive
                or player.pending_respawn
                or player.attempt_started_game is None
            ):
                continue
            attempt_age = self.last_game_time - player.attempt_started_game
            allowed = max(minimum, record.best_seconds * multiplier)
            if not math.isfinite(attempt_age) or attempt_age < allowed:
                continue
            if (
                player.last_checkpoint_game is not None
                and self.last_game_time - player.last_checkpoint_game
                <= checkpoint_grace
            ):
                continue
            candidates.append(player)
        return candidates

    async def _run_final_countdown(
        self,
        resume: bool = False,
        enforce_clock_runout: bool = False,
    ) -> None:
        if (
            not self.current
            or self.transitioning
            or getattr(self, "controller_reload_draining", False)
        ):
            return
        map_key = self.current.key
        records = self.store.records(map_records_key(self.current))
        duration = final_countdown_seconds(records)
        if enforce_clock_runout:
            # The last-run window follows the full respawn-enabled map window.
            # Cap that additional window independently at the configured map
            # maximum (five minutes by default).
            duration = min(duration, self._map_play_seconds(self.current))
        # Route certification can take tens of seconds on unusually complex
        # maps. Arm and announce the countdown immediately; build its progress
        # guard in a worker thread while racers continue their runs.
        self._schedule_final_countdown_guard(duration)
        now = time.time()

        if not resume or not self.final_countdown_end_epoch:
            self.final_countdown_active = True
            self._clear_all_votes()
            self.final_countdown_end_epoch = now + duration
            self.final_countdown_map_key = map_key
            self.store.set_json("final_countdown_active", True)
            self.store.set_json(
                "final_countdown_end_epoch", self.final_countdown_end_epoch
            )
            self.store.set_json("final_countdown_map_key", map_key)
            # Establish the eligible racers before the first await so a held
            # cycle released concurrently with the announcement is retained.
            self.finalists = {
                id(player)
                for player in self.active_players()
                if player.alive and player.respawn_enabled
            }
            await self._disable_practice_for_countdown()
            runout_players = (
                self._clock_runout_players(records)
                if enforce_clock_runout
                else []
            )
            if runout_players:
                self.finalists.difference_update(map(id, runout_players))
                for player in runout_players:
                    await self.private(
                        player,
                        "Your run exceeded the clock-runout limit for this map.",
                    )
                await self.sink.send(
                    *(f"KILL_SILENT {player.target}" for player in runout_players)
                )
                LOG.info(
                    "clock runout prevention map=%s players=%s",
                    map_key,
                    ",".join(player.identity_key for player in runout_players),
                )
            for task in self.respawn_tasks.values():
                task.cancel()
            self.respawn_tasks.clear()
            for task in self.freeze_tasks.values():
                task.cancel()
            self.freeze_tasks.clear()
            for player in self.players.values():
                if (
                    player.pending_respawn
                    and player.respawn_created_game is None
                ):
                    player.generation += 1
                    player.pending_respawn = False
            announcement = (
                getattr(self, "final_countdown_announcement", None)
                or "Map time expired."
            )
            self.final_countdown_announcement = None
            rating_summary = self.store.rating_summary(self.current.rating_key)
            await self.broadcast_messages(
                f"{announcement} Respawning is disabled. "
                f"Final countdown: {math.ceil(duration)} seconds.",
                format_final_countdown_rating_message(rating_summary),
            )
            LOG.info(
                "final countdown map=%s duration=%.3f record=%s",
                map_key,
                duration,
                f"{records[0].best_seconds:.3f}" if records else "none",
            )
        else:
            self.finalists = {
                id(player)
                for player in self.active_players()
                if player.alive and player.respawn_enabled
            }
            await self._disable_practice_for_countdown()
        highest_number = max(
            1,
            math.ceil(
                float(
                    getattr(self, "final_countdown_duration_seconds", 0.0)
                    or duration
                )
            ),
        )
        last_number: int | None = None
        while (
            self.final_countdown_active
            and self.current
            and self.current.key == map_key
            and not self.transitioning
            and not getattr(self, "controller_reload_draining", False)
        ):
            if not self._alive_finalists():
                await self.broadcast("All remaining racers are finished.")
                await self.activate_next_map("all racers finished final countdown")
                return
            if getattr(self, "finishes_in_progress", set()):
                await asyncio.sleep(0.01)
                continue
            remaining = float(self.final_countdown_end_epoch or now) - time.time()
            if remaining <= 0:
                await self.sink.send(
                    final_countdown_center_command(0, highest_number)
                )
                await self.activate_next_map("final countdown expired")
                return
            number = max(1, math.ceil(remaining))
            if number != last_number:
                await self.sink.send(
                    final_countdown_center_command(number, highest_number)
                )
                last_number = number
            await asyncio.sleep(0.1)

    async def _handle_command(self, payload: str) -> None:
        parsed = parse_intercepted_command(payload)
        if not parsed:
            return
        command, player_name, access_level, arguments = parsed
        player = self.player_for(player_name)
        if not player:
            # Unknown command senders may be spectators missed during a
            # controller restart.  Let them queue/query maps, but do not count
            # them as active voters until a grid/online event confirms it.
            player = Player(player_name, player_name, connected=True, active=False)
            self._start_mode_for(player)
            self.players[player_name.casefold()] = player
            self.register_alias(player, player_name)
        self._publish_player_audit(
            "command",
            player,
            command=command,
        )
        await self._dispatch_command(command, player, access_level, arguments)

    async def _dispatch_command(
        self,
        command: str,
        player: Player,
        access_level: int,
        arguments: str,
    ) -> None:
        if not await self._command_rate_allowed(player):
            return
        hot_commands = getattr(self, "hot_commands", None)
        if hot_commands and await hot_commands.dispatch(
            self, command, player, access_level, arguments
        ):
            return
        if command == "/q":
            await self._command_queue(player, arguments)
        elif command == "/rate":
            await self._command_rate(player, arguments)
        elif command == "/help":
            await self._command_help(player, access_level, arguments)
        elif command == "/report":
            await self._command_report(player, arguments, access_level)
        elif command == "/suggest":
            await self._command_suggest(player, arguments, access_level)
        elif command == "/leaderboard":
            await self._command_leaderboard(player)
        elif command == "/results":
            await self._command_results(player)
        elif command == "/ghost":
            await self._command_ghost(player, arguments)
        elif command == "/setspawn":
            await self._command_setspawn(player, arguments)
        elif command == "/start":
            await self._command_start(player, arguments)
        elif command == "/practice":
            await self._command_practice(player, arguments)
        elif command == "/link":
            await self._command_link(player, arguments)
        elif command == "/cp":
            await self._command_checkpoint_respawn(player)
        elif command == "/restart":
            await self._command_restart(player)
        elif command == "/extend":
            await self._command_extend(player)
        elif command == "/skip":
            await self._command_skip(player)
        elif command == "/forceskip":
            await self._command_forceskip(player, access_level)
        elif command == "/end":
            await self._command_end(player, access_level)
        elif command == "/nextmap":
            await self._command_nextmap(player)
        elif command == "/rotation":
            await self._command_rotation(player)
        elif command == "/exclusion_list":
            await self._command_exclusion_list(player)
        elif command in {"/respawn", "/sui"}:
            await self._command_respawn(player, kill_first=True)
        elif command == "/join":
            await self._command_respawn(player, kill_first=False)
        elif command in {"/spec", "/spectate"}:
            await self._command_spectate(player)
        elif command == "/size":
            await self._command_size(player, access_level, arguments)
        elif command == "/reloadmaps":
            await self._command_reloadmaps(player, access_level)
        elif command == "/resetalltimes":
            await self._command_reset_all_times(player, access_level)
        elif command == "/reset":
            await self._command_reset_time(player, access_level, arguments)
        elif command == "/message":
            await self._command_message(player, access_level, arguments)
        elif command == "/review":
            await self._command_review(player, access_level, arguments)
        elif command == "/exclude":
            await self._command_exclude(player, access_level, arguments)
        elif command == "/remove_exclusion":
            await self._command_remove_exclusion(player, access_level, arguments)

    async def _command_queue(self, player: Player, query: str) -> None:
        query = query.strip()
        usage = (
            "Usage: /q add [map name], /q lowest, /q remove [map], or /q clear"
        )
        if not query:
            await self.private(player, usage)
            return

        action, separator, action_query = query.partition(" ")
        action = action.casefold()
        action_query = action_query.strip() if separator else ""
        if action == "clear":
            if action_query:
                await self.private(player, usage)
                return
            removed_count = len(self.queue)
            if not removed_count:
                await self.private(player, "The map queue is already empty.")
                return
            self.queue.clear()
            self.queue_attribution = {}
            self._save_rotation()
            await self.broadcast(
                f"{player.record_name} cleared {removed_count} "
                f"{'map' if removed_count == 1 else 'maps'} from the queue."
            )
            return

        if action == "lowest":
            if action_query:
                await self.private(player, usage)
                return
            await self._queue_lowest_ranked_map(player)
            return

        if action not in {"add", "remove"}:
            await self.private(
                player,
                "The map queue format changed: use /q add [map name]. " + usage,
            )
            return

        removing = action == "remove"
        query = action_query
        if not query:
            await self.private(player, f"Usage: /q {action} [map name]")
            return

        matches = self.repository.search(query)
        if not matches:
            await self.private(player, f"No map found matching: {query}")
            return

        if removing:
            queued_keys = set(self.queue)
            queued_matches = [entry for entry in matches if entry.key in queued_keys]
            if not queued_matches:
                await self.private(player, f"That map is not in the queue: {query}")
                return
            matches = queued_matches

        if len(matches) > 1:
            preview = ", ".join(
                f"{self._display_map_name(entry)} ({entry.author})"
                for entry in matches[:5]
            )
            await self.private(player, f"Map name is ambiguous: {preview}")
            return

        entry = matches[0]
        display_name = self._display_map_name(entry)
        if removing:
            position = list(self.queue).index(entry.key) + 1
            self.queue.remove(entry.key)
            if entry.key not in self.queue:
                getattr(self, "queue_attribution", {}).pop(entry.key, None)
            self._save_rotation()
            await self.broadcast(
                f"{player.record_name} removed {display_name} by {entry.author} "
                f"from the queue (was position {position})."
            )
            return

        if self.current and entry.key == self.current.key:
            await self.private(
                player,
                f"{display_name} is already active and cannot be queued next.",
            )
            return

        self.queue.append(entry.key)
        self._attribute_queued_map(entry.key, player.record_name, "server")
        self._save_rotation()
        await self.broadcast(
            f"{player.record_name} queued {display_name} by {entry.author} "
            f"(position {len(self.queue)})."
        )

    async def _queue_lowest_ranked_map(self, player: Player) -> None:
        unavailable = set(self.queue)
        if self.current:
            unavailable.add(self.current.key)
        candidates = [
            entry
            for entry in self.repository.catalog.values()
            if entry.key not in unavailable
        ]
        if not candidates:
            await self.private(
                player,
                "Every available map is already active or in the queue.",
            )
            return

        ranks = self.store.map_ranks_for_player(
            (map_records_key(entry) for entry in candidates),
            player.identity_key,
        )
        unranked = [
            entry for entry in candidates if map_records_key(entry) not in ranks
        ]
        if unranked:
            choices = unranked
            rank_text = "unranked"
        else:
            lowest_rank = max(ranks[map_records_key(entry)] for entry in candidates)
            choices = [
                entry
                for entry in candidates
                if ranks[map_records_key(entry)] == lowest_rank
            ]
            rank_text = f"rank {lowest_rank}"
        entry = random.choice(choices)
        self.queue.append(entry.key)
        self._attribute_queued_map(entry.key, player.record_name, "server")
        self._save_rotation()
        await self.broadcast(
            f"{player.record_name} queued their lowest-ranked map, "
            f"{self._display_map_name(entry)} by {entry.author} "
            f"({rank_text}; position {len(self.queue)})."
        )

    async def _command_rate(self, player: Player, argument: str) -> None:
        requested = argument.strip().casefold()
        entry = self.current

        if requested in {"undo", "revoke"} and not entry:
            await self.private(player, "No current map is available to rate.")
            return

        if requested not in {"undo", "revoke"}:
            parsed = re.fullmatch(r"(?:(.+?)\s+)?([1-5])", argument.strip())
            if not parsed:
                await self.private(
                    player,
                    "Usage: /rate [1-5], /rate [map] [1-5], "
                    "/rate undo, or /rate revoke",
                )
                return
            map_query, requested_rating = parsed.groups()
            if map_query:
                matches = self.repository.search(map_query)
                if not matches:
                    await self.private(
                        player, f"No map found matching: {map_query}"
                    )
                    return
                if len(matches) > 1:
                    preview = ", ".join(
                        f"{self._display_map_name(item)} ({item.author})"
                        for item in matches[:5]
                    )
                    await self.private(
                        player, f"Map name is ambiguous: {preview}"
                    )
                    return
                entry = matches[0]
            requested = requested_rating

        if not entry:
            await self.private(player, "No current map is available to rate.")
            return
        map_key = entry.rating_key
        map_name = self._display_map_name(entry)

        if requested == "undo":
            result = self.store.undo_rating(map_key, player.identity_key)
            if result is None:
                await self.private(
                    player,
                    f"There is no rating change to undo for {map_name}.",
                )
                return
            _, restored = result
            if restored is None:
                await self.private(
                    player,
                    f"Your rating for {map_name} was undone and removed.",
                )
            else:
                await self.private(
                    player,
                    f"Your rating for {map_name} was restored to {restored}/5.",
                )
            return

        if requested == "revoke":
            revoked = self.store.revoke_rating(map_key, player.identity_key)
            if revoked is None:
                await self.private(
                    player,
                    f"You have no rating to revoke for {map_name}.",
                )
            else:
                await self.private(
                    player,
                    f"Your {revoked}/5 rating for {map_name} was revoked.",
                )
            return

        if not re.fullmatch(r"[1-5]", requested):
            await self.private(
                player,
                "Usage: /rate [1-5], /rate [map] [1-5], "
                "/rate undo, or /rate revoke",
            )
            return
        rating = int(requested)
        _, changed = self.store.set_rating(map_key, player, rating)
        if not changed:
            await self.private(
                player,
                f"You already rated {map_name} {rating}/5.",
            )
            return
        await self.broadcast(
            f"{player.record_name} rated {map_name} {rating}/5. "
            "Use /rate to submit your own rating."
        )

    async def _command_help(
        self,
        player: Player,
        access_level: int,
        search_term: str = "",
    ) -> None:
        entries = list(USER_COMMAND_HELP)
        for setting, command, description in ADMIN_COMMAND_HELP:
            if access_level <= int(self.config.get(setting, 1)):
                entries.append((command, description))
        hot_commands = getattr(self, "hot_commands", None)
        if hot_commands:
            entries.extend(hot_commands.help_entries(self.config, access_level))
        query = " ".join(plain_console_text(search_term).split())[:80]
        if query:
            entries = search_help_entries(entries, query)
            if not entries:
                await self.private(
                    player,
                    f'No commands match "{query}". Use /help to list all commands.',
                )
                return
            heading = f'TronnerRacing commands matching "{query}":'
        else:
            heading = "TronnerRacing commands:"
        await self.private_block(
            player,
            [heading, *build_help_lines(entries)],
        )

    def _saved_message_recipient(self, query: str) -> StoredIdentity:
        target = plain_console_text(query).strip()
        if not target or any(character.isspace() for character in target):
            raise ValueError("Choose one player name or exact auth:name identity.")
        folded = target.casefold()
        players = {
            id(item): item for item in getattr(self, "players", {}).values()
        }.values()
        direct: dict[str, StoredIdentity] = {}
        fallback: dict[str, StoredIdentity] = {}
        for candidate in players:
            if not candidate.auth_name:
                continue
            identity = self.store.identity_for_player(candidate)
            if candidate.auth_name.casefold() == folded:
                direct[identity.identity_key.casefold()] = identity
            if folded in {
                candidate.log_name.casefold(),
                plain_console_text(candidate.display_name).strip().casefold(),
            }:
                fallback[identity.identity_key.casefold()] = identity
        connected_matches = direct or fallback
        if len(connected_matches) == 1:
            return next(iter(connected_matches.values()))
        if len(connected_matches) > 1:
            raise ValueError(
                "That player name is ambiguous; use their exact auth:name identity."
            )

        stored = [
            identity
            for identity in self.store.matching_user_identities(target)
            if identity.authenticated and identity.identity_key.startswith("auth:")
        ]
        if len(stored) == 1:
            return stored[0]
        if len(stored) > 1:
            raise ValueError("That saved player name is ambiguous; use auth:name.")

        explicit = self.store.explicit_user_identity(target)
        if explicit and explicit.authenticated:
            return explicit
        if "@" in target:
            return StoredIdentity(f"auth:{folded}", target, True)
        raise ValueError(
            "Authenticated player not found. Use their current name or exact "
            "auth:name identity."
        )

    async def _command_message(
        self,
        player: Player,
        access_level: int,
        arguments: str,
    ) -> None:
        maximum_access = int(self.config.get("records_admin_access_level", 1))
        if access_level > maximum_access:
            await self.private(player, "Administrator access is required for /message.")
            return
        target, separator, raw_message = arguments.strip().partition(" ")
        message = plain_console_text(raw_message).strip()
        if not target or not separator or not message:
            await self.private(player, "Usage: /message [player] [message]")
            return
        if len(message) > PLAYER_MESSAGE_LIMIT:
            await self.private(
                player,
                f"Messages may be at most {PLAYER_MESSAGE_LIMIT} characters.",
            )
            return
        try:
            recipient = self._saved_message_recipient(target)
            saved = self.store.save_player_message(
                recipient,
                self.store.identity_for_player(player),
                message,
            )
        except (ValueError, OverflowError) as exc:
            await self.private(player, str(exc))
            return
        await self.private(
            player,
            f"Message queued for {saved.recipient_name}'s next authenticated login.",
        )
        self._publish_player_audit(
            "offline_message_queued",
            player,
            target=saved.recipient_name,
            message=saved.message,
        )

    async def _deliver_saved_player_messages(self, player: Player) -> int:
        if not player.auth_name:
            return 0
        delivered = 0
        for saved in self.store.pending_player_messages(player.identity_key):
            timestamp = datetime.datetime.fromtimestamp(
                saved.created_at,
                tz=datetime.timezone.utc,
            ).strftime("%Y-%m-%d %H:%M UTC")
            await self.private(
                player,
                f"Saved message from {saved.sender_name} ({timestamp}): "
                f"{saved.message}",
            )
            if self.store.delete_player_message(saved.id, player.identity_key):
                delivered += 1
                self._publish_player_audit(
                    "offline_message_delivered",
                    player,
                    target=saved.sender_name,
                    message=saved.message,
                )
        return delivered

    def _report_api_key(self) -> str:
        api_key = os.environ.get("RESEND_API_KEY", "").strip()
        if api_key:
            return api_key
        configured_path = self.config.get("resend_api_key_file")
        if not configured_path:
            return ""
        try:
            return Path(configured_path).read_text(encoding="utf-8").strip()
        except OSError:
            return ""

    async def _command_report(
        self,
        player: Player,
        argument: str,
        access_level: int,
        *,
        submission_type: str = "report",
    ) -> None:
        is_suggestion = submission_type == "suggestion"
        config_prefix = "suggest" if is_suggestion else "report"
        command_name = "/suggest" if is_suggestion else "/report"
        singular = "suggestion" if is_suggestion else "report"
        plural = "Suggestions" if is_suggestion else "Reports"
        maximum_characters = max(
            1,
            int(
                self.config.get(
                    f"{config_prefix}_maximum_characters",
                    self.config.get("report_maximum_characters", 1000),
                )
            ),
        )
        message = plain_console_text(argument).strip()
        if not message:
            await self.private(player, f"Usage: {command_name} [message]")
            return
        if len(message) > maximum_characters:
            await self.private(
                player,
                f"{plural} may be at most {maximum_characters} characters.",
            )
            return

        api_key = self._report_api_key()
        recipient = str(
            self.config.get(
                f"{config_prefix}_recipient",
                self.config.get("report_recipient", ""),
            )
        ).strip()
        sender = str(
            self.config.get(
                f"{config_prefix}_sender",
                self.config.get("report_sender", ""),
            )
        ).strip()
        if not api_key or not recipient or not sender:
            LOG.error("%s service configuration is unavailable", singular)
            await self.private(
                player,
                f"{plural} are temporarily unavailable. Please try again later.",
            )
            return

        now_monotonic = time.monotonic()
        maximum_admin_access = int(
            self.config.get(
                f"{config_prefix}_admin_access_level",
                self.config.get("report_admin_access_level", 1),
            )
        )
        if access_level <= maximum_admin_access:
            cooldown_seconds = max(
                0.0,
                float(
                    self.config.get(
                        f"{config_prefix}_admin_cooldown_seconds",
                        self.config.get("report_admin_cooldown_seconds", 30),
                    )
                ),
            )
        else:
            cooldown_seconds = max(
                0.0,
                float(
                    self.config.get(
                        f"{config_prefix}_cooldown_seconds",
                        self.config.get("report_cooldown_seconds", 300),
                    )
                ),
            )
        last_sent = self.report_last_sent.get(player.identity_key)
        if last_sent is not None and now_monotonic - last_sent < cooldown_seconds:
            remaining = max(
                1,
                math.ceil(cooldown_seconds - (now_monotonic - last_sent)),
            )
            await self.private(
                player,
                f"Please wait {remaining} seconds before sending another {singular}.",
            )
            return

        now_epoch = time.time()
        quota_window_seconds = max(
            1.0,
            float(self.config.get("report_quota_window_seconds", 31 * 86400)),
        )
        quota_maximum = max(
            1, int(self.config.get("report_quota_maximum", 240))
        )
        while (
            self.report_success_epochs
            and now_epoch - self.report_success_epochs[0] >= quota_window_seconds
        ):
            self.report_success_epochs.popleft()
        if len(self.report_success_epochs) >= quota_maximum:
            LOG.warning("email submission service quota guard reached")
            await self.private(
                player,
                "The report and suggestion limit has been reached. "
                "Please contact an admin directly.",
            )
            return

        username = clean_console_text(
            plain_console_text(player.display_name or player.log_name)
        )[:80] or "Unknown"
        authenticated_username = clean_console_text(
            plain_console_text(player.auth_name or "Not authenticated")
        )[:120] or "Not authenticated"
        timezone_name = str(
            self.config.get(
                f"{config_prefix}_timezone",
                self.config.get("report_timezone", "America/Phoenix"),
            )
        )
        try:
            report_timezone = ZoneInfo(timezone_name)
        except ZoneInfoNotFoundError:
            LOG.warning("unknown report timezone %r; using UTC", timezone_name)
            report_timezone = datetime.timezone.utc
        reported_at = datetime.datetime.now(report_timezone)
        timestamp = reported_at.strftime("%Y-%m-%d %H:%M:%S %Z")
        subject_label = "Feature suggestion" if is_suggestion else "Report"
        subject = (
            f"[{timestamp}] {subject_label} from {username} "
            f"(auth: {authenticated_username})"
        )
        map_name = (
            self._display_map_name(self.current) if self.current else "Unknown"
        )
        body_label = "Feature Suggestion" if is_suggestion else "Player Report"
        message_label = "Suggestion" if is_suggestion else "Report"
        body = (
            f"Tronner Racing {body_label}\n"
            "\n"
            f"Submitted: {timestamp}\n"
            f"Display username: {username}\n"
            f"Authenticated username: {authenticated_username}\n"
            f"Current map: {map_name}\n"
            "\n"
            f"{message_label}:\n"
            f"{message}\n"
        )
        try:
            await asyncio.to_thread(
                send_resend_report,
                api_key,
                recipient,
                sender,
                subject,
                body,
                str(self.config.get("resend_endpoint", RESEND_ENDPOINT)),
                max(
                    1.0,
                    float(
                        self.config.get(
                            f"{config_prefix}_timeout_seconds",
                            self.config.get("report_timeout_seconds", 10),
                        )
                    ),
                ),
            )
        except Exception as error:
            LOG.warning(
                "%s submission failed for username=%r auth=%r: %s",
                singular,
                username,
                authenticated_username,
                error,
            )
            await self.private(
                player,
                f"Unable to send your {singular} right now. Please try again later.",
            )
            return

        self.report_last_sent[player.identity_key] = now_monotonic
        self.report_success_epochs.append(now_epoch)
        self.store.set_json(
            "report_success_epochs", list(self.report_success_epochs)
        )
        LOG.info(
            "%s submitted for username=%r auth=%r",
            singular,
            username,
            authenticated_username,
        )
        await self.private(player, f"Your {singular} was sent. Thank you.")

    async def _command_suggest(
        self,
        player: Player,
        argument: str,
        access_level: int,
    ) -> None:
        await self._command_report(
            player,
            argument,
            access_level,
            submission_type="suggestion",
        )

    async def _command_leaderboard(self, player: Player) -> None:
        if not self.current:
            await self.private(player, "No current map is available.")
            return
        records = self.store.records(map_records_key(self.current))
        lines, _ = build_leaderboard_table(
            self._display_map_name(self.current),
            self.current.author,
            records,
            top_limit=10,
            axes=self.current.axes,
            rating=self.store.rating_average(self.current.rating_key),
            time_decimals=race_time_decimals(self.current),
        )
        await self.private_block(player, lines)

    def _ghost_replay_map_keys(self) -> tuple[str, ...]:
        if not self.current:
            return ()
        record_key = map_records_key(self.current)
        keys = {record_key, self.current.key}
        try:
            aliases = self._replay_record_key_aliases()
        except AttributeError:
            aliases = {}
        keys.update(
            resource_key
            for resource_key, target_key in aliases.items()
            if target_key == record_key
        )
        return tuple(sorted(key for key in keys if key))

    @staticmethod
    def _unverified_ghost_coordinate_scale(
        recorded_size_factor: float | None,
        current_size_factor: float | None,
    ) -> float:
        """Best-effort scale used when historical geometry cannot be verified."""
        try:
            recorded = float(recorded_size_factor or 0.0)
            current = float(current_size_factor or 0.0)
            if not all(math.isfinite(value) and abs(value) <= 100 for value in (recorded, current)):
                return 1.0
            scale = 2.0 ** ((recorded - current) / 2.0)
            return scale if math.isfinite(scale) and scale > 1e-12 else 1.0
        except (TypeError, ValueError, OverflowError):
            return 1.0

    @staticmethod
    def _ghost_record_for_selector(
        records: Sequence[Record],
        player: Player,
        argument: str,
    ) -> tuple[Record | None, int | None, str]:
        requested = plain_console_text(argument).strip()
        parts = requested.split(maxsplit=1)
        selector = parts[0].casefold() if parts else ""
        value = parts[1].strip() if len(parts) > 1 else ""
        if selector in {"", "pb", "personal", "personalbest"}:
            for rank, record in enumerate(records, 1):
                if record.identity_key == player.identity_key:
                    return record, rank, "PB"
            return None, None, "You do not have a recorded finish on this map."
        if selector in {"wr", "world", "worldrecord"}:
            if records:
                return records[0], 1, "WR"
            return None, None, "This map does not have a world record yet."
        if selector == "rank" or selector.isdigit():
            rank_text = value if selector == "rank" else selector
            if not rank_text.isdigit() or int(rank_text) <= 0:
                return None, None, "Usage: /ghost rank [positive number]"
            rank = int(rank_text)
            if rank > len(records):
                return None, None, f"This map currently has only {len(records)} ranked finishes."
            return records[rank - 1], rank, f"rank {rank}"
        if selector in {"player", "name"}:
            query = value
        else:
            query = requested
        folded = query.casefold()
        if not folded:
            return None, None, "Usage: /ghost player [exact player name]"
        exact = [
            (rank, record)
            for rank, record in enumerate(records, 1)
            if record.username.casefold() == folded
            or record.identity_key.casefold() == folded
            or record.identity_key.removeprefix("auth:").casefold() == folded
        ]
        matches = exact or [
            (rank, record)
            for rank, record in enumerate(records, 1)
            if folded in record.username.casefold()
        ]
        if not matches:
            return None, None, f"No ranked player matches: {query}"
        if len(matches) > 1:
            preview = ", ".join(record.username for _, record in matches[:5])
            return None, None, f"Player name is ambiguous: {preview}"
        rank, record = matches[0]
        return record, rank, record.username

    def _write_ghost_plan(
        self,
        replay: GhostReplay,
        label: str,
    ) -> str:
        directory = Path(
            self.config.get(
                "ghost_plan_dir", "/var/lib/armagetronad/ghosts"
            )
        )
        filename = f"ghost-{os.getpid()}-{time.time_ns()}.plan"
        if not GHOST_PLAN_FILENAME_RE.fullmatch(filename):
            raise RuntimeError("unable to create a safe ghost plan name")
        safe_label = plain_console_text(label).encode("ascii", "replace")[
            :GHOST_LEGACY_NAME_BYTES
        ]
        duration_us = round(replay.finish_seconds * 1_000_000)
        plan_format = (
            GHOST_PLAN_FORMAT_VERSION
            if any(state is not None for state in replay.event_states)
            else 1
        )
        event_lines = []
        for event_index, (offset_us, action) in enumerate(replay.events):
            state = (
                replay.event_states[event_index]
                if event_index < len(replay.event_states)
                else None
            )
            line = f"EVENT {offset_us} {action}"
            if plan_format >= 2:
                if state is None:
                    line += " 0"
                else:
                    line += " 1 " + " ".join(
                        (
                            format(state.x, ".17g"),
                            format(state.y, ".17g"),
                            format(state.xdir, ".17g"),
                            format(state.ydir, ".17g"),
                            format(state.speed, ".17g"),
                            str(state.turns),
                        )
                    )
            event_lines.append(line)
        lines = [
            f"TRONNER_GHOST {plan_format}",
            f"RUN {replay.run_id}",
            f"NAME {safe_label.hex() or '-'}",
            f"DURATION_US {duration_us}",
            "START "
            + " ".join(
                (
                    format(replay.x, ".17g"),
                    format(replay.y, ".17g"),
                    format(replay.xdir, ".17g"),
                    format(replay.ydir, ".17g"),
                    format(replay.speed, ".17g"),
                    str(replay.initial_turns),
                )
            ),
            f"EVENT_COUNT {len(replay.events)}",
            *event_lines,
            "END",
        ]
        atomic_write_text(directory / filename, "\n".join(lines))
        return filename

    async def _refresh_ghost_selections(self, record_key: str) -> None:
        """Re-resolve active or persistent selections after a saved run."""
        if not self.current or map_records_key(self.current) != record_key:
            return
        seen_players: set[int] = set()
        for player in list(getattr(self, "players", {}).values()):
            if (
                id(player) in seen_players
                or not player.connected
                or player.is_ai
            ):
                continue
            seen_players.add(id(player))
            state = getattr(self, "ghost_selections", {}).get(player.identity_key)
            selector = (
                plain_console_text(state.get("selector", ""))
                if isinstance(state, dict)
                else getattr(self, "ghost_preferences", {}).get(
                    player.identity_key, ""
                )
            )
            if selector:
                await self._command_ghost(player, selector, automatic=True)

    async def _command_ghost(
        self,
        player: Player,
        argument: str,
        *,
        automatic: bool = False,
        silent: bool = False,
    ) -> bool:
        requested = (plain_console_text(argument).strip() or "pb")[:128]
        if requested.casefold() in {"off", "none", "clear"}:
            await self.sink.send(f"GHOST_CLEAR {player.target}")
            getattr(self, "ghost_selections", {}).pop(player.identity_key, None)
            preferences = getattr(self, "ghost_preferences", {})
            if player.identity_key in preferences:
                preferences.pop(player.identity_key, None)
                self._save_ghost_preferences()
            if not automatic:
                await self.private(player, "Your replay ghost is disabled.")
            return True
        persistent_selector = normalize_ghost_preference(requested)
        if persistent_selector is not None:
            requested = persistent_selector
            if not automatic:
                if not hasattr(self, "ghost_preferences"):
                    self.ghost_preferences = {}
                self.ghost_preferences[player.identity_key] = requested
                self._save_ghost_preferences()
        if not self.current or not self.round_active or self.transitioning:
            if not automatic:
                if persistent_selector is not None:
                    await self.private(
                        player,
                        "Your ghost preference was saved and will apply when a map is active.",
                    )
                else:
                    await self.private(player, "A replay ghost requires an active map.")
            return False
        records = self.store.records(map_records_key(self.current))
        record, rank, selection = self._ghost_record_for_selector(
            records, player, requested
        )
        unfinished_pb = False
        if record is None or rank is None:
            if requested != "pb":
                if not automatic:
                    await self.private(player, selection)
                return False
            replays = self.store.ghost_replays_for_unfinished_pb(
                map_records_key(self.current),
                player.identity_key,
                self._ghost_replay_map_keys(),
            )
            if not replays:
                if not automatic:
                    await self.private(
                        player,
                        "Your PB ghost is enabled, but you do not have a usable "
                        "attempt on this map yet.",
                    )
                return False
            replay = replays[0]
            unfinished_pb = True
            selection = "PB"
            target_identity_key = replay.identity_key
            target_username = replay.username
        else:
            replays = self.store.ghost_replays_for_record(
                map_records_key(self.current),
                record,
                self._ghost_replay_map_keys(),
            )
            replay = replays[0] if replays else None
            target_identity_key = record.identity_key
            target_username = record.username
        if not replays:
            if not automatic:
                await self.private(
                    player,
                    f"The {selection} time has no captured full-run replay.",
                )
            return False
        active_settings = getattr(
            self, "active_replay_settings_identifier", None
        )
        assert replay is not None
        position_scale = self.repository.ghost_coordinate_scale(
            self.current,
            replay.resource_key,
            replay.size_factor,
            self.current_size_factor,
        )
        geometry_verified = position_scale is not None
        if position_scale is None:
            position_scale = self._unverified_ghost_coordinate_scale(
                replay.size_factor,
                self.current_size_factor,
            )
        physics_verified = not (
            active_settings is not None
            and replay.settings_identifiers
            and any(
                not self.store.ghost_settings_compatible(
                    identifier,
                    active_settings,
                    ignore_size_factor=True,
                )
                for identifier in replay.settings_identifiers
            )
        )
        if not geometry_verified or not physics_verified:
            LOG.warning(
                "loading unverified replay ghost map=%s run=%d player=%s "
                "geometry_verified=%s physics_verified=%s",
                map_records_key(self.current),
                replay.run_id,
                target_identity_key,
                geometry_verified,
                physics_verified,
            )
        if replay.speed <= 1e-12:
            recovered_speed = next(
                (
                    speed
                    for identifier in (
                        replay.settings_identifier,
                        active_settings,
                    )
                    if (speed := self.store.ghost_start_speed(identifier))
                    is not None
                ),
                None,
            )
            if recovered_speed is None:
                try:
                    recovered_speed = float(
                        self.config.get("ghost_legacy_start_speed", 20.0)
                    )
                except (TypeError, ValueError):
                    recovered_speed = 20.0
            if not math.isfinite(recovered_speed) or recovered_speed <= 1e-12:
                recovered_speed = 20.0
            LOG.info(
                "using recovered start speed %.6g for legacy ghost run %d",
                recovered_speed,
                replay.run_id,
            )
            replay = dataclasses.replace(replay, speed=recovered_speed)
        replay = dataclasses.replace(
            replay,
            x=replay.x * position_scale,
            y=replay.y * position_scale,
            event_states=tuple(
                dataclasses.replace(
                    state,
                    x=state.x * position_scale,
                    y=state.y * position_scale,
                )
                if state is not None
                else None
                for state in replay.event_states
            ),
        )
        label = ghost_display_name(
            target_username,
            personal_best=target_identity_key == player.identity_key,
        )
        resolved_selection = {
            "selector": requested,
            "runId": replay.run_id,
            "rank": rank or 0,
            "recordIdentityKey": target_identity_key,
            "ghostName": label,
        }
        previous_selection = getattr(self, "ghost_selections", {}).get(
            player.identity_key
        )
        if automatic and previous_selection == resolved_selection:
            return True
        try:
            filename = self._write_ghost_plan(replay, label)
        except OSError:
            LOG.exception("unable to write replay ghost plan")
            if not automatic:
                await self.private(
                    player, "The replay ghost could not be prepared right now."
                )
            return False
        try:
            await self.sink.send(f"GHOST_LOAD {player.target} {filename}")
        except Exception:
            with contextlib.suppress(OSError):
                (
                    Path(
                        self.config.get(
                            "ghost_plan_dir", "/var/lib/armagetronad/ghosts"
                        )
                    )
                    / filename
                ).unlink()
            raise
        if not hasattr(self, "ghost_selections"):
            self.ghost_selections = {}
        self.ghost_selections[player.identity_key] = resolved_selection
        if not automatic and persistent_selector is None:
            preferences = getattr(self, "ghost_preferences", {})
            if player.identity_key in preferences:
                preferences.pop(player.identity_key, None)
                self._save_ghost_preferences()
        decimals = race_time_decimals(self.current)
        exact_ranked_run = (
            record is not None
            and replay.finish_seconds == record.best_seconds
            and replay.finish_turns == record.best_turns
        )
        if unfinished_pb:
            message = "Selected PB: your closest unfinished attempt. "
        elif exact_ranked_run:
            message = (
                f"Selected {selection}: {target_username}, "
                f"{record.best_seconds:.{decimals}f}s. "
            )
        else:
            message = (
                f"Selected fastest available replay for {selection}: "
                f"{target_username}, {replay.finish_seconds:.{decimals}f}s "
                f"(ranked time {record.best_seconds:.{decimals}f}s). "
            )
        if automatic and not silent:
            if unfinished_pb:
                await self.private(
                    player,
                    "Your PB ghost was updated to your closest unfinished "
                    "attempt. It will start with your next attempt.",
                )
            else:
                await self.private(
                    player,
                    f"Your {selection} ghost was updated to {target_username}, "
                    f"{replay.finish_seconds:.{decimals}f}s. It will start with "
                    "your next attempt.",
                )
        elif not automatic:
            await self.private(
                player,
                message + "The private ghost will start with your next attempt.",
            )
        return True

    async def _command_results(self, player: Player) -> None:
        enabled = not self.result_message_preferences.get(
            player.identity_key, True
        )
        self.result_message_preferences[player.identity_key] = enabled
        self.store.set_json(
            "result_message_preferences", self.result_message_preferences
        )
        await self.private(
            player,
            "Finish and rank messages are now "
            + ("visible." if enabled else "hidden. Use /results to show them again."),
        )

    async def _command_setspawn(self, player: Player, argument: str) -> None:
        if not self.current or not self.current.spawns:
            await self.private(player, "The current map has no selectable spawns.")
            return
        requested = argument.strip()
        if requested:
            try:
                number = int(requested)
            except ValueError:
                await self.private(
                    player,
                    f"Usage: /setspawn [0-{len(self.current.spawns)}] (0 clears it)",
                )
                return
            if number == 0:
                stable_key = map_spawn_preferences_key(self.current)
                map_preferences = self._spawn_preferences_for(self.current)
                removed = map_preferences.pop(player.identity_key, None)
                if not map_preferences:
                    self.spawn_preferences.pop(stable_key, None)
                if removed is not None:
                    self._save_spawn_preferences()
                if (
                    player.last_spawn_index is not None
                    and 0 <= player.last_spawn_index < len(self.current.spawns)
                ):
                    player.spawn_cursor = (
                        player.last_spawn_index + 1
                    ) % len(self.current.spawns)
                else:
                    player.spawn_cursor = 0
                if removed is None:
                    await self.private(
                        player,
                        f"You do not have a saved spawn for "
                        f"{self._display_map_name(self.current)}.",
                    )
                else:
                    await self.private(
                        player,
                        f"Saved spawn removed for "
                        f"{self._display_map_name(self.current)}.",
                    )
                return
        elif (
            player.last_spawn_index is not None
            and 0 <= player.last_spawn_index < len(self.current.spawns)
        ):
            number = player.last_spawn_index + 1
        else:
            await self.private(
                player,
                "No recent spawn is available. Use /setspawn followed by a spawn number.",
            )
            return
        if not 1 <= number <= len(self.current.spawns):
            await self.private(
                player,
                f"Spawn must be between 1 and {len(self.current.spawns)}.",
            )
            return
        map_preferences = self._spawn_preferences_for(self.current, create=True)
        map_preferences[player.identity_key] = number
        self._save_spawn_preferences()
        player.spawn_cursor = number - 1
        await self.private(
            player,
            f"Spawn #{number} saved for "
            f"{self._display_map_name(self.current)}. It will be used "
            "for every respawn on this map.",
        )

    async def _command_start(self, player: Player, argument: str) -> None:
        requested = argument.strip().casefold()
        if not requested:
            mode = self._start_mode_for(player)
            delay = player.start_respawn_delay_seconds
            delay_text = "instant" if delay == 0 else f"{delay:g} seconds"
            await self.private(
                player,
                f"Start mode: {mode}. Respawn wait: {delay_text}. "
                "Usage: /start [brake|immediate|countdown|respawn] "
                "[respawn seconds, default 0].",
            )
            return
        preference = normalize_start_preference(requested)
        if preference is None:
            await self.private(
                player,
                "Usage: /start [brake|immediate|countdown|respawn] "
                "[respawn seconds, default 0]. Respawn seconds must be "
                "between 0 and 60.",
            )
            return
        mode, respawn_delay, preference = start_preference_details(preference)
        player.start_mode = mode
        player.start_respawn_delay_seconds = respawn_delay
        if not hasattr(self, "start_preferences"):
            self.start_preferences = {}
        self.start_preferences[player.identity_key] = preference
        self._save_start_preferences()
        descriptions = {
            "brake": "Press brake to begin moving after each respawn.",
            "immediate": "Begin moving immediately after each automatic respawn.",
            "countdown": "Wait for a 3-second countdown and Go!.",
            "respawn": "Wait after a crash, then begin immediately when you use /restart.",
        }
        delay_text = (
            "instantly"
            if respawn_delay == 0
            else f"after {respawn_delay:g} seconds"
        )
        pending = (
            " Your current start is unchanged; this applies on your next respawn."
            if player.pending_respawn
            else ""
        )
        await self.private(
            player,
            f"Start mode set to {mode}; respawn {delay_text}. "
            f"{descriptions[mode]}{pending}",
        )

    async def _command_practice(self, player: Player, argument: str) -> None:
        usage = (
            "Usage: /practice reset [seconds], /practice maintain [seconds], "
            "or /practice off."
        )
        parts = argument.strip().casefold().split()
        if not parts:
            if self._practice_active(player):
                await self.private(
                    player,
                    f"Practice mode: {player.practice_mode}, rewinding "
                    f"{player.practice_rewind_seconds:g} seconds after death. "
                    "No times are recorded. " + usage,
                )
            else:
                await self.private(player, "Practice mode is off. " + usage)
            return
        if parts[0] == "off":
            if len(parts) != 1:
                await self.private(player, usage)
                return
            was_active = self._practice_active(player)
            current_life_tainted = bool(
                player.alive and player.practice_attempt_tainted
            )
            self._clear_player_practice(
                player,
                preserve_current_attempt=current_life_tainted,
            )
            await self.private(
                player,
                (
                    "Practice mode disabled. This life still cannot record a "
                    "time; your next life can."
                    if current_life_tainted
                    else "Practice mode disabled."
                )
                if was_active
                else "Practice mode is already off.",
            )
            return
        if len(parts) != 2 or parts[0] not in PRACTICE_MODES:
            await self.private(player, usage)
            return
        try:
            rewind_seconds = float(parts[1])
        except ValueError:
            await self.private(player, usage)
            return
        maximum = max(
            0.0,
            float(
                self.config.get(
                    "practice_max_rewind_seconds",
                    DEFAULT_PRACTICE_MAX_REWIND_SECONDS,
                )
            ),
        )
        if (
            not math.isfinite(rewind_seconds)
            or rewind_seconds < 0
            or rewind_seconds > maximum
        ):
            await self.private(
                player,
                f"Practice rewind must be from 0 to {maximum:g} seconds.",
            )
            return
        if not self.current or not self.round_active or self.transitioning:
            await self.private(player, "Practice mode requires an active map.")
            return
        if self.final_countdown_active or getattr(
            self, "server_restart_active", False
        ):
            await self.private(
                player,
                "Practice mode cannot be enabled during a countdown.",
            )
            return
        player.practice_mode = parts[0]
        player.practice_rewind_seconds = rewind_seconds
        player.practice_map_key = self.current.key
        player.practice_samples.clear()
        player.practice_respawn_snapshot = None
        player.practice_start_respawn_pending = False
        player.practice_finish_pending = False
        player.practice_attempt_tainted = True
        self.next_activity_probe_monotonic = 0.0
        await self.sink.send("GET_PLAYER_ACTIVITY")
        speed_text = (
            "Speed will be reset to 0"
            if player.practice_mode == "reset"
            else "Speed will be restored"
        )
        await self.private(
            player,
            f"Practice mode enabled for {self._display_map_name(self.current)}. "
            f"Deaths rewind {rewind_seconds:g} seconds. {speed_text}, your "
            "/start setting is used, and finishes do not record a time. "
            "A manual respawn returns to the map start.",
        )

    def _game_link_secret(self) -> str:
        secret = os.environ.get("GAME_LINK_SERVER_SECRET", "").strip()
        if secret:
            return secret
        game_link = self.config.get("game_link", {})
        if not isinstance(game_link, dict):
            return ""
        configured_path = str(
            game_link.get(
                "secret_file",
                "/etc/tronner-racing/game-link-secret",
            )
        ).strip()
        if not configured_path:
            return ""
        try:
            return Path(configured_path).read_text(encoding="utf-8").strip()
        except OSError:
            return ""

    async def _command_link(self, player: Player, argument: str) -> None:
        code = plain_console_text(argument).strip()
        if not re.fullmatch(r"\d{6}", code):
            await self.private(
                player,
                "Usage: /link [6-digit code]. Generate one under Game logins "
                "in your tronner.io settings.",
            )
            return
        game_username = plain_console_text(player.auth_name or "").strip()
        if not game_username:
            await self.private(
                player,
                "Sign in to your in-game account first, then use /link again.",
            )
            return
        game_link = self.config.get("game_link", {})
        if not isinstance(game_link, dict):
            game_link = {}
        endpoint = str(
            game_link.get("endpoint", DEFAULT_GAME_LINK_ENDPOINT)
        ).strip()
        secret = self._game_link_secret()
        server_id = str(
            game_link.get("server_id", self.server_id)
        ).strip().casefold()
        if not endpoint or not secret or not server_id:
            LOG.error("game account linking is not configured")
            await self.private(
                player,
                "Account linking is temporarily unavailable. Please try again later.",
            )
            return
        try:
            result = await asyncio.to_thread(
                redeem_game_account_link,
                endpoint,
                secret,
                code,
                game_username,
                server_id,
                max(1.0, float(game_link.get("timeout_seconds", 10))),
            )
        except GameLinkServiceError as error:
            LOG.info(
                "game account link refused for auth=%r server=%s reason=%s",
                game_username,
                server_id,
                error.code,
            )
            await self.private(player, error.public_message)
            return
        except Exception as error:
            LOG.warning(
                "game account link failed for auth=%r server=%s: %s",
                game_username,
                server_id,
                error,
            )
            await self.private(
                player,
                "Unable to link your account right now. Please try again later.",
            )
            return
        website_name = clean_console_text(
            result.get("websiteDisplayName", "your website account")
        ).strip()[:80] or "your website account"
        website_uid = clean_console_text(result.get("websiteUid", ""))[:128]
        self._publish_player_audit(
            "account_link",
            player,
            websiteUid=website_uid,
            websiteName=website_name,
        )
        await self.private(
            player,
            f"Linked {game_username} to {website_name} on tronner.io.",
        )

    async def _command_extend(self, player: Player) -> None:
        if not self.current or not self._round_is_active():
            await self.private(player, "No active map is available to extend.")
            return
        if self.transitioning:
            await self.private(player, "A map change is already in progress.")
            return
        voters = self.eligible_voters()
        voter_ids = {id(voter) for voter in voters}
        if id(player) not in voter_ids:
            await self.private(player, "Only active players may vote to extend.")
            return
        active_keys = {voter.identity_key for voter in voters}
        self.extend_votes.intersection_update(active_keys)
        count = max(1, len(voters))
        required = 1 if count == 1 else extend_votes_required(count)
        self.extend_votes.add(player.identity_key)
        if not await self._resolve_extend_vote():
            await self.broadcast(
                f"Extend vote: {len(self.extend_votes)}/{required} required."
            )

    async def _command_skip(self, player: Player) -> None:
        if not self.current or not self._round_is_active():
            await self.private(player, "No active map is available to skip.")
            return
        if self.transitioning:
            await self.private(player, "A map change is already in progress.")
            return
        if self.final_countdown_active or self.final_countdown_announcement:
            await self.private(player, "The end-of-map timer is already active.")
            return
        voters = self.eligible_voters()
        voter_ids = {id(voter) for voter in voters}
        if id(player) not in voter_ids:
            await self.private(player, "Only active players may vote to skip.")
            return
        active_keys = {voter.identity_key for voter in voters}
        self.skip_votes.intersection_update(active_keys)
        count = max(1, len(voters))
        required = 1 if count == 1 else skip_votes_required(count)
        self.skip_votes.add(player.identity_key)
        if not await self._resolve_skip_vote():
            await self.broadcast(
                f"Skip vote: {len(self.skip_votes)}/{required} required. "
                "Type /skip to go to the next map"
            )

    async def _command_end(self, player: Player, access_level: int) -> None:
        maximum_access = int(self.config.get("map_admin_access_level", 1))
        if access_level > maximum_access:
            await self.private(
                player, "Only an Owner or Admin may start the end-of-map timer."
            )
            return
        if not self.current or not self._round_is_active():
            await self.private(player, "No active map is available to end.")
            return
        if self.transitioning:
            await self.private(player, "A map change is already in progress.")
            return
        if self.final_countdown_active or self.final_countdown_announcement:
            await self.private(player, "The end-of-map timer is already active.")
            return

        idle_seconds = float(
            self.config.get("final_countdown_idle_seconds", 10)
        )
        if idle_seconds > 0 and not self._final_countdown_progress_guard_enabled():
            # Clear racers who were already idle at the instant /end was
            # submitted. The final-countdown loop keeps rechecking afterward.
            await self.sink.send(
                f"KILL_IDLE_PLAYERS {idle_seconds:.9g}"
            )

        # Map timer owns the countdown loop. Expiring its ordinary deadline
        # keeps /end indistinguishable from a natural timer expiration.
        self.final_countdown_announcement = None
        self.deadline_epoch = time.time()
        self.store.set_json("deadline_epoch", self.deadline_epoch)

    async def _command_forceskip(self, player: Player, access_level: int) -> None:
        maximum_access = int(self.config.get("records_admin_access_level", 1))
        if access_level > maximum_access:
            await self.private(player, "Only an Owner or Admin may force-skip maps.")
            return
        if self.transitioning:
            await self.private(player, "A map change is already in progress.")
            return
        self._clear_vote("skip")
        await self.broadcast(f"{player.record_name} force-skipped the map.")
        await self.activate_next_map("admin force skip")

    async def _command_exclusion_list(self, player: Player) -> None:
        rows = self._excluded_map_rows()
        if not rows:
            await self.private(player, "The exclusion list is empty.")
            return
        reasons = getattr(self, "excluded_map_reasons", {})
        items = [
            f"{selector} by {author} [{version}]"
            + (f" — {reasons[key]}" if reasons.get(key) else "")
            for key, _, author, version, selector in rows
        ]
        await self.private_block(
            player,
            [
                f"Excluded maps ({len(rows)}):",
                *build_compact_columns(items),
            ],
        )

    async def _map_reviews(self) -> list[dict]:
        return await asyncio.to_thread(self.repository.list_map_reviews)

    async def _command_review_list(self, player: Player) -> None:
        try:
            rows = self._review_map_rows(await self._map_reviews())
        except Exception as exc:
            LOG.exception("loading the Vectron map review list failed")
            await self.private(player, f"Review list failed: {exc}")
            return
        if not rows:
            await self.private(player, "The map review list is empty.")
            return
        items = [
            f"{selector} by {author} [{version}; {status}]"
            for _, _, _, author, version, status, selector in rows
        ]
        await self.private_block(
            player,
            [
                f"Maps awaiting or needing Vectron review ({len(rows)}):",
                *build_compact_columns(items),
            ],
        )

    async def _command_review_remove(
        self,
        player: Player,
        query: str,
    ) -> None:
        if not query.strip():
            await self.private(player, "Usage: /review remove [map name]")
            return
        try:
            reviews = await self._map_reviews()
        except Exception as exc:
            LOG.exception("loading the Vectron map review list failed")
            await self.private(player, f"Review removal failed: {exc}")
            return
        matches = self._search_map_reviews(reviews, query)
        if not matches:
            await self.private(player, f"No reviewed map found matching: {query.strip()}")
            return
        if len(matches) > 1:
            preview = ", ".join(
                f"{selector} ({author}, {version})"
                for _, _, _, author, version, _, selector in matches[:5]
            )
            await self.private(player, f"Reviewed map name is ambiguous: {preview}")
            return
        review_id, key, name, author, version, _, selector = matches[0]
        if (
            self.current
            and key == self.current.key
            and (self.final_countdown_active or self.final_countdown_announcement)
        ):
            await self.private(
                player,
                "That map is already ending; remove it from review after the next map starts.",
            )
            return
        async with self.map_lock:
            try:
                await asyncio.to_thread(
                    self.repository.cancel_map_review,
                    review_id,
                    f"Review cancelled by server admin {player.record_name}",
                )
                self._reconcile_rotation()
            except Exception as exc:
                LOG.exception("cancelling map review failed for %s", review_id)
                await self.private(player, f"Review removal failed: {exc}")
                return
        await self.broadcast(
            f"{player.record_name} removed {selector} by {author} [{version}] "
            "from review and returned it to the map pool."
        )

    async def _command_review_submit(
        self,
        player: Player,
        query: str,
        reason: str = "",
    ) -> None:
        query = query.strip()
        if query:
            matches = self.repository.search(query)
            if not matches:
                await self.private(player, f"No active map found matching: {query}")
                return
            if len(matches) > 1:
                preview = ", ".join(
                    f"{self._display_map_name(entry)} ({entry.author}, {entry.version})"
                    for entry in matches[:5]
                )
                await self.private(player, f"Map name is ambiguous: {preview}")
                return
            entry = matches[0]
        else:
            entry = self.current
            if not entry:
                await self.private(player, "No current map is available for review.")
                return

        reviewing_current = bool(self.current and entry.key == self.current.key)
        if reviewing_current:
            if not self._round_is_active():
                await self.private(player, "The current map has not started yet.")
                return
            if self.transitioning:
                await self.private(player, "A map change is already in progress.")
                return
            if self.final_countdown_active or self.final_countdown_announcement:
                await self.private(player, "The end-of-map timer is already active.")
                return
        if len(set(self.repository.catalog) - {entry.key}) < 1:
            await self.private(player, "The final available map cannot be reviewed.")
            return

        name = self._display_map_name(entry)
        submission_reason = (
            reason.strip()
            or f"Submitted by server admin {player.record_name}"
        )
        async with self.map_lock:
            try:
                await asyncio.to_thread(
                    self.repository.submit_map_review,
                    entry.key,
                    submission_reason,
                )
                self._reconcile_rotation()
            except Exception as exc:
                LOG.exception("submitting map review failed for %s", entry.key)
                await self.private(player, f"Review submission failed: {exc}")
                return

        await self.broadcast(
            f"{player.record_name} submitted {name} by {entry.author} "
            "for Vectron review and removed it from rotation."
        )
        if reviewing_current:
            # Arm the countdown before yielding again so no respawn can slip
            # in after a map has been removed from the catalog.
            self.final_countdown_active = True
            self.final_countdown_end_epoch = None
            self.final_countdown_map_key = entry.key
            self.final_countdown_announcement = "Map submitted for Vectron review."
            self.store.set_json("final_countdown_active", True)
            self.store.set_json("final_countdown_end_epoch", None)
            self.store.set_json("final_countdown_map_key", entry.key)
            await self._disable_practice_for_countdown()
            idle_seconds = float(
                self.config.get("final_countdown_idle_seconds", 10)
            )
            if (
                idle_seconds > 0
                and not self._final_countdown_progress_guard_enabled()
            ):
                await self.sink.send(f"KILL_IDLE_PLAYERS {idle_seconds:.9g}")

    async def _command_review(
        self,
        player: Player,
        access_level: int,
        arguments: str,
    ) -> None:
        maximum_access = int(self.config.get("map_admin_access_level", 1))
        if access_level > maximum_access:
            await self.private(player, "Only an Owner or Admin may review maps.")
            return
        action, separator, remainder = arguments.strip().partition(" ")
        if action.casefold() == "list" and not remainder.strip():
            await self._command_review_list(player)
        elif action.casefold() == "remove":
            await self._command_review_remove(
                player,
                remainder.strip() if separator else "",
            )
        else:
            query, reason, has_reason = split_admin_reason(arguments)
            if has_reason and not reason:
                await self.private(
                    player,
                    "Enter a reason after --, or omit -- entirely.",
                )
                return
            if len(reason) > 1000:
                await self.private(
                    player,
                    "Keep the review reason to 1,000 characters or fewer.",
                )
                return
            await self._command_review_submit(player, query, reason)

    async def _command_remove_exclusion(
        self,
        player: Player,
        access_level: int,
        query: str,
    ) -> None:
        maximum_access = int(self.config.get("map_admin_access_level", 1))
        if access_level > maximum_access:
            await self.private(
                player,
                "Only an Owner or Admin may remove map exclusions.",
            )
            return
        query = query.strip()
        if not query:
            await self.private(player, "Usage: /remove_exclusion [map name]")
            return
        matches = self._search_excluded_maps(query)
        if not matches:
            await self.private(player, f"No excluded map found matching: {query}")
            return
        if len(matches) > 1:
            preview = ", ".join(
                f"{selector} ({author}, {version})"
                for _, _, author, version, selector in matches[:5]
            )
            await self.private(player, f"Excluded map name is ambiguous: {preview}")
            return

        key, _, author, version, selector = matches[0]
        exclusion_reason = getattr(self, "excluded_map_reasons", {}).get(key, "")
        async with self.map_lock:
            try:
                await asyncio.to_thread(
                    publish_repository_map_status,
                    self.repository,
                    key,
                    "active",
                    f"Reactivated by server admin {player.record_name}",
                )
            except Exception as exc:
                LOG.exception("publishing map reactivation failed for %s", key)
                await self.private(player, f"Removing exclusion failed: {exc}")
                return
            self.excluded_map_keys.remove(key)
            if hasattr(self, "excluded_map_reasons"):
                self.excluded_map_reasons.pop(key, None)
            self.repository.excluded_keys = self.excluded_map_keys
            self.store.set_json(
                "excluded_map_keys",
                sorted(self.excluded_map_keys),
            )
            self.store.set_json(
                "excluded_map_reasons",
                getattr(self, "excluded_map_reasons", {}),
            )
            try:
                await asyncio.to_thread(self.repository.scan)
                self._reconcile_rotation()
            except Exception as exc:
                self.excluded_map_keys.add(key)
                if exclusion_reason:
                    self.excluded_map_reasons[key] = exclusion_reason
                self.repository.excluded_keys = self.excluded_map_keys
                self.store.set_json(
                    "excluded_map_keys",
                    sorted(self.excluded_map_keys),
                )
                self.store.set_json(
                    "excluded_map_reasons",
                    getattr(self, "excluded_map_reasons", {}),
                )
                LOG.exception("removing map exclusion failed for %s", key)
                await self.private(player, f"Removing exclusion failed: {exc}")
                return
        await self.broadcast(
            f"{player.record_name} returned {selector} by {author} "
            f"[{version}] to the map pool."
        )

    async def _command_exclude(
        self,
        player: Player,
        access_level: int,
        arguments: str = "",
    ) -> None:
        maximum_access = int(self.config.get("map_admin_access_level", 1))
        if access_level > maximum_access:
            await self.private(player, "Only an Owner or Admin may exclude maps.")
            return
        query, reason, has_reason = split_admin_reason(arguments)
        if has_reason and not reason:
            await self.private(
                player,
                "Enter a reason after --, or omit -- entirely.",
            )
            return
        if len(reason) > 1000:
            await self.private(
                player,
                "Keep the exclusion reason to 1,000 characters or fewer.",
            )
            return
        if query:
            matches = self.repository.search(query)
            if not matches:
                await self.private(player, f"No active map found matching: {query}")
                return
            if len(matches) > 1:
                preview = ", ".join(
                    f"{self._display_map_name(entry)} ({entry.author}, {entry.version})"
                    for entry in matches[:5]
                )
                await self.private(player, f"Map name is ambiguous: {preview}")
                return
            entry = matches[0]
        else:
            entry = self.current
            if not entry:
                await self.private(player, "No current map is available.")
                return
        excluding_current = bool(self.current and entry.key == self.current.key)
        if excluding_current and self.transitioning:
            await self.private(player, "A map change is already in progress.")
            return
        key = entry.key
        if len(set(self.repository.catalog) - {key}) < 1:
            await self.private(player, "The final available map cannot be excluded.")
            return
        name = self._display_map_name(entry)
        status_reason = (
            reason.strip()
            or f"Excluded by server admin {player.record_name}"
        )
        try:
            await asyncio.to_thread(
                publish_repository_map_status,
                self.repository,
                key,
                "inactive",
                status_reason,
            )
        except Exception as exc:
            LOG.exception("publishing map exclusion failed for %s", key)
            await self.private(player, f"Excluding map failed: {exc}")
            return
        await self._exclude_map_key(key, status_reason)
        await self.broadcast(
            f"{player.record_name} excluded {name} from the map pool."
            + (f" Reason: {reason}" if reason else "")
        )
        if excluding_current:
            await self.activate_next_map("admin excluded current map")

    async def _command_reset_all_times(
        self, player: Player, access_level: int
    ) -> None:
        maximum_access = int(self.config.get("records_admin_access_level", 1))
        if access_level > maximum_access:
            await self.private(player, "Only an Owner or Admin may reset times.")
            return
        if not self.current:
            await self.private(player, "No current map is available.")
            return
        record_count, finish_count = self.store.reset_map(map_records_key(self.current))
        await self.broadcast(
            f"{player.record_name} reset all times on "
            f"{self._display_map_name(self.current)}: "
            f"{record_count} records and {finish_count} finish entries removed."
        )

    async def _command_reset_time(
        self, player: Player, access_level: int, arguments: str
    ) -> None:
        maximum_access = int(self.config.get("records_admin_access_level", 1))
        if access_level > maximum_access:
            await self.private(player, "Only an Owner or Admin may reset times.")
            return
        username, separator, map_query = arguments.strip().partition(" ")
        if not username:
            await self.private(player, "Usage: /reset [user] [map (optional)]")
            return
        if separator:
            matches = self.repository.search(map_query)
            if not matches:
                await self.private(player, f"No map found matching: {map_query}")
                return
            if len(matches) > 1:
                preview = ", ".join(
                    f"{self._display_map_name(entry)} ({entry.author})"
                    for entry in matches[:5]
                )
                await self.private(player, f"Map name is ambiguous: {preview}")
                return
            entry = matches[0]
        else:
            entry = self.current
        if not entry:
            await self.private(player, "No current map is available.")
            return
        names, record_count, finish_count = self.store.reset_user(
            map_records_key(entry), username
        )
        if not names:
            await self.private(
                player,
                f"No record for {username} was found on "
                f"{self._display_map_name(entry)}.",
            )
            return
        matched_names = ", ".join(names)
        await self.broadcast(
            f"{player.record_name} reset {matched_names} on "
            f"{self._display_map_name(entry)}: "
            f"{record_count} record and {finish_count} finish entries removed."
        )

    async def _command_nextmap(self, player: Player) -> None:
        entry = self._peek_next()
        if entry:
            prefix = "Queued next" if self.queue else "Next map"
            await self.private(
                player,
                f"{prefix}: {self._display_map_name(entry)} by {entry.author}",
            )
        else:
            await self.private(player, "No map is currently available.")

    async def _command_rotation(self, player: Player) -> None:
        entries_by_key = dict(self.repository.catalog)
        if self.current:
            entries_by_key.setdefault(self.current.key, self.current)
        entries = sorted(
            entries_by_key.values(),
            key=lambda entry: (
                self._display_map_name(entry).casefold(),
                entry.author.casefold(),
                entry.version.casefold(),
                entry.key.casefold(),
            ),
        )
        if not entries:
            await self.private(player, "The map rotation is empty.")
            return
        current_key = self.current.key if self.current else None
        items = [
            (
                self._display_map_name(entry),
                entry.author,
                entry.version,
                entry.key == current_key,
            )
            for entry in entries
        ]
        await self.private_block(
            player,
            [
                f"Map rotation ({len(entries)}):",
                *build_rotation_columns(items),
            ],
        )

    async def _command_reloadmaps(
        self, player: Player, access_level: int
    ) -> None:
        maximum_access = int(self.config.get("map_admin_access_level", 1))
        if access_level > maximum_access:
            await self.private(player, "Only an Owner or Admin may reload maps.")
            return
        async with self.map_lock:
            before = set(self.repository.catalog)
            try:
                await asyncio.to_thread(self.repository.sync, True)
                self._reconcile_rotation()
            except Exception as exc:
                LOG.exception("manual map reload failed")
                await self.private(player, f"Map reload failed: {exc}")
                return
            after = set(self.repository.catalog)
        added = sorted(after - before)
        removed = sorted(before - after)
        await self.private(
            player,
            f"Maps reloaded: {len(after)} available, {len(added)} added, "
            f"{len(removed)} removed.",
        )
        if added:
            labels = ", ".join(
                self._display_map_name(self.repository.catalog[key])
                for key in added
            )
            await self.private(player, f"Added: {labels}")

    async def _command_size(
        self, player: Player, access_level: int, argument: str
    ) -> None:
        maximum_access = int(self.config.get("size_admin_access_level", 1))
        if access_level > maximum_access:
            await self.private(player, "Only an Owner or Admin may change map size.")
            return
        match = re.fullmatch(r"([+-])(\d+(?:\.\d+)?)", argument.strip())
        if not match:
            await self.private(player, "Usage: /size +x or /size -x")
            return
        if not self.current:
            await self.private(player, "No active map is available to revise.")
            return
        if not self._round_is_active():
            await self.private(player, "The current map has not started yet.")
            return
        if self.transitioning:
            await self.private(player, "A map change is already in progress.")
            return
        if self.final_countdown_active or self.final_countdown_announcement:
            await self.private(player, "The end-of-map timer is already active.")
            return
        delta = float(match.group(2)) * (1 if match.group(1) == "+" else -1)
        current_factor = self.current_size_factor
        if current_factor is None:
            with contextlib.suppress(Exception):
                current_factor = await asyncio.to_thread(
                    self.repository.map_size_factor, self.current
                )
        if current_factor is None:
            current_factor = float(self.config.get("default_size_factor", 0))
        revised_factor = current_factor + delta
        if not math.isfinite(revised_factor) or not -10 <= revised_factor <= 10:
            await self.private(player, "SIZE_FACTOR must remain between -10 and 10.")
            return

        await self.private(
            player,
            f"Publishing map size {format_size_factor(current_factor)} -> "
            f"{format_size_factor(revised_factor)}...",
        )

        async with self.map_lock:
            old_entry = self.current
            try:
                # Firebase swaps the catalog snapshot after publishing the new
                # immutable revision. Preserve the currently loaded XML in the
                # engine cache so countdown route checks and reload recovery can
                # still read the old revision until the transition completes.
                await asyncio.to_thread(
                    self.repository.cache_for_server, old_entry
                )
                preserved_old_entry = old_entry
                cache_dir = getattr(self.repository, "cache_dir", None)
                if isinstance(old_entry, MapEntry) and cache_dir is not None:
                    cached_old_path = Path(cache_dir) / old_entry.key
                    if cached_old_path.is_file():
                        preserved_old_entry = dataclasses.replace(
                            old_entry,
                            local_path=cached_old_path,
                        )
                revision = await asyncio.to_thread(
                    self.repository.create_size_revision, old_entry, revised_factor
                )
                old_entry = preserved_old_entry
                self.current = preserved_old_entry
                # Firebase advances the logical map document to a new immutable
                # resource path, so its superseded path is already absent from
                # rotation. Only the legacy Git backend needs a local exclusion.
                if getattr(self.repository, "firebase", None) is None:
                    self.excluded_map_keys.add(old_entry.key)
                    self.repository.excluded_keys = self.excluded_map_keys
                    self.store.set_json(
                        "excluded_map_keys", sorted(self.excluded_map_keys)
                    )
                if getattr(self.repository, "firebase", None) is None:
                    await asyncio.to_thread(self.repository.scan)
                revision = self.repository.catalog[revision.key]
                self._reconcile_rotation()
                with contextlib.suppress(ValueError):
                    self.rotation.remove(revision.key)
                self.queue = collections.deque(
                    key
                    for key in self.queue
                    if key not in {old_entry.key, revision.key}
                )
                self.queue.appendleft(revision.key)
                self._attribute_queued_map(
                    revision.key, player.record_name, "server"
                )
                self._save_rotation()
                await asyncio.to_thread(self.repository.cache_for_server, revision)
            except Exception as exc:
                LOG.exception("unable to create SIZE_FACTOR map revision")
                await self.private(player, f"Unable to revise this map: {exc}")
                return

            self.pending_size_change = {
                "source_map_key": old_entry.key,
                "target_map_key": revision.key,
                "source_records_key": map_records_key(old_entry),
                "target_records_key": map_records_key(revision),
            }
            self.store.set_json(
                "pending_size_change", self.pending_size_change
            )

            # Keep the current grid alive and use the established final-countdown
            # path to disable respawns and give active racers one last run. The
            # protected pending target makes the new immutable revision next even
            # if an administrator edits the ordinary map queue in the meantime.
            self.final_countdown_active = True
            self.final_countdown_end_epoch = None
            self.final_countdown_map_key = old_entry.key
            self.final_countdown_announcement = (
                f"Map size changed from {format_size_factor(current_factor)} to "
                f"{format_size_factor(revised_factor)}."
            )
            self.store.set_json("final_countdown_active", True)
            self.store.set_json("final_countdown_end_epoch", None)
            self.store.set_json("final_countdown_map_key", old_entry.key)
            await self._disable_practice_for_countdown()
            idle_seconds = float(
                self.config.get("final_countdown_idle_seconds", 10)
            )
            if (
                idle_seconds > 0
                and not self._final_countdown_progress_guard_enabled()
            ):
                await self.sink.send(f"KILL_IDLE_PLAYERS {idle_seconds:.9g}")
            await self.broadcast(
                f"{player.record_name} resized "
                f"{self._display_map_name(revision)} from "
                f"{format_size_factor(current_factor)} to "
                f"{format_size_factor(revised_factor)}. Version "
                f"{revision.version} will load after the final countdown."
            )

    async def _command_checkpoint_respawn(self, player: Player) -> None:
        if self._practice_active(player):
            await self._command_practice_start_respawn(player)
            return
        if getattr(self, "respawns_paused", False):
            await self.private(
                player,
                "Respawns are paused for a server script reload; your run will resume shortly.",
            )
            return
        if self.final_countdown_active:
            await self.private(
                player,
                "Checkpoint respawns are disabled during the final countdown.",
            )
            return
        snapshot = player.checkpoint_snapshot
        if snapshot is None:
            await self.private(player, "No checkpoint is available for this run yet.")
            return
        if not player.connected or not player.active or not player.respawn_enabled:
            await self.private(player, "Join the grid before using /cp.")
            return

        now = time.monotonic()
        repeat_window = max(
            0.0,
            float(self.config.get("checkpoint_double_respawn_seconds", 1.5)),
        )
        double_respawn = player.pending_respawn_kind == "checkpoint" or (
            player.last_checkpoint_respawn_monotonic is not None
            and now - player.last_checkpoint_respawn_monotonic <= repeat_window
        )
        player.last_checkpoint_respawn_monotonic = now
        player.checkpoint_respawn_requested = True
        player.checkpoint_respawn_speed = 0.0 if double_respawn else snapshot.speed
        self._cancel_player_freeze(player, clear_attempt=False)
        player.pending_respawn_kind = ""

        if double_respawn:
            await self.private(
                player,
                "Checkpoint respawn reset: takeoff speed is now 0.",
            )
        if player.alive:
            await self.sink.send(f"KILL_SILENT {player.target}")
            return
        self._schedule_respawn(
            player,
            delay_seconds=float(
                self.config.get("checkpoint_respawn_delay_seconds", 0.1)
            ),
        )

    async def _command_spectate(self, player: Player) -> None:
        player.respawn_enabled = False
        player.forced_racing = False
        self.finalists.discard(id(player))
        self._cancel_player_freeze(player)
        await self.private(player, "Respawning disabled. Use /join or /respawn to return.")
        if player.alive:
            await self.sink.send(f"KILL_SILENT {player.target}")

    async def _command_restart(self, player: Player) -> None:
        if self._practice_active(player):
            await self._command_practice_start_respawn(player)
            return
        if getattr(self, "respawns_paused", False):
            await self.private(
                player,
                "Respawns are paused for a server script reload; your run will resume shortly.",
            )
            return
        if self.final_countdown_active:
            await self.private(
                player,
                "Respawning is disabled during the final countdown.",
            )
            return
        player.respawn_enabled = True
        if not player.connected:
            await self.private(player, "Join the grid before restarting.")
            return
        if not player.active:
            player.forced_racing = True
            player.active = True
        self._cancel_player_freeze(player)
        if self._start_mode_for(player) == "respawn":
            player.manual_restart_pending = True
            await self.center_private(player, "")
        if player.alive:
            await self.sink.send(f"KILL_SILENT {player.target}")
            return
        if id(player) not in self.respawn_tasks:
            self._schedule_respawn(
                player,
                delay_seconds=player.start_respawn_delay_seconds,
            )

    async def _command_respawn(self, player: Player, kill_first: bool) -> None:
        if self._practice_active(player) and (kill_first or not player.alive):
            await self._command_practice_start_respawn(player)
            return
        if getattr(self, "respawns_paused", False):
            await self.private(
                player,
                "Respawns are paused for a server script reload; your run will resume shortly.",
            )
            return
        if self.final_countdown_active:
            await self.private(player, "Respawning is disabled during the final countdown.")
            if kill_first and player.alive:
                self.finalists.discard(id(player))
                await self.sink.send(f"KILL_SILENT {player.target}")
            return
        player.respawn_enabled = True
        if not player.connected:
            await self.private(player, "Join the grid before enabling respawns.")
            return
        if not player.active:
            # RESPAWN_STRICT is disabled for this controller-managed path, so a
            # client retaining spectator mode can explicitly return to racing.
            player.forced_racing = True
            player.active = True
        if kill_first and player.alive:
            self._cancel_player_freeze(player, clear_attempt=False)
            await self.sink.send(f"KILL_SILENT {player.target}")
            return
        if not player.alive and id(player) not in self.respawn_tasks:
            await self._respawn_player(player)
        elif not player.alive:
            await self.private(player, "Respawn already scheduled.")
        else:
            await self.private(player, "Respawning enabled.")

    async def _command_practice_start_respawn(self, player: Player) -> None:
        if getattr(self, "respawns_paused", False):
            await self.private(
                player,
                "Respawns are paused for a server script reload; your run will resume shortly.",
            )
            return
        if self.final_countdown_active:
            await self.private(
                player, "Respawning is disabled during the final countdown."
            )
            return
        if not player.connected:
            await self.private(player, "Join the grid before respawning.")
            return
        player.respawn_enabled = True
        if not player.active:
            player.forced_racing = True
            player.active = True
        self._cancel_player_freeze(player)
        player.practice_start_respawn_pending = True
        player.practice_respawn_snapshot = None
        player.practice_samples.clear()
        player.practice_finish_pending = False
        player.manual_restart_pending = True
        if player.alive:
            await self.sink.send(f"KILL_SILENT {player.target}")
            return
        await self._respawn_player(player)

    async def _announce_time_left(self, now: float) -> None:
        if (
            not self._round_is_active()
            or self.transitioning
            or self.final_countdown_active
            or self.deadline_epoch is None
        ):
            return
        minute = max(0, int(math.ceil((self.deadline_epoch - now) / 60.0)))
        if minute == self.last_time_left_minute:
            return
        self.last_time_left_minute = minute
        if minute > 0 and minute % 2 == 0:
            await self.broadcast(f"Time left: {minute} minutes.")

    async def map_timer(self) -> None:
        while not self.stop_event.is_set():
            if getattr(self, "controller_reload_draining", False):
                await asyncio.sleep(0.25)
                continue
            if self.final_countdown_active:
                await self._run_final_countdown(resume=True)
            elif self._round_is_active() and not self.transitioning:
                now = time.time()
                await self._announce_time_left(now)
                if self.deadline_epoch is not None and now >= self.deadline_epoch:
                    await self._run_final_countdown(enforce_clock_runout=True)
            await asyncio.sleep(0.25)

    async def repository_refresher(self) -> None:
        # Firebase invalidation is handled by catalog_state_monitor. Retain the
        # periodic refresher only for legacy Git-backed repositories.
        if (
            self.repository.firebase is not None
            or not self.config.get("repository_auto_sync", True)
        ):
            await self.stop_event.wait()
            return
        interval = max(60, int(self.config.get("repository_refresh_seconds", 300)))
        while not self.stop_event.is_set():
            await asyncio.sleep(interval)
            try:
                async with self.map_lock:
                    await asyncio.to_thread(self.repository.sync)
                    self._reconcile_rotation()
            except Exception:
                LOG.exception("repository refresh failed; retaining the current catalog")

    async def catalog_state_monitor(self) -> None:
        """Watch one version document instead of polling full collections."""
        if self.repository.firebase is None:
            await self.stop_event.wait()
            return
        interval = max(
            5.0,
            float(self.config.get(
                "catalog_state_poll_seconds",
                self.config.get("review_status_poll_seconds", 15),
            )),
        )
        while not self.stop_event.is_set():
            try:
                firebase = self.repository.firebase
                state = await asyncio.to_thread(firebase.get_catalog_state)
                signature = (
                    int(state.get("catalogVersion") or 0),
                    str(state.get("generation") or ""),
                    str(state.get("serverManifestSha256") or ""),
                )
                if not all(signature):
                    raise FirebaseCatalogError(
                        "catalog state is incomplete; retaining the current catalog"
                    )
                if signature != self.catalog_state_signature:
                    async with self.map_lock:
                        manifest = await asyncio.to_thread(
                            self.repository.sync,
                            catalog_state=state,
                        )
                        self._reconcile_rotation()
                    self.catalog_state_signature = signature
                    LOG.info(
                        "Firebase catalog version %d applied (generation %s)",
                        signature[0],
                        signature[1],
                    )
                else:
                    manifest = None
                if signature != self.catalog_ack_signature:
                    if manifest is None:
                        manifest = json.loads(
                            (self.repository.checkout / ".catalog.json").read_text("utf-8")
                        )
                    await asyncio.to_thread(
                        firebase.publish_server_catalog_state,
                        catalog_state=state,
                        generation=str(manifest.get("generation") or ""),
                        map_count=len(manifest.get("maps") or []),
                    )
                    self.catalog_ack_signature = signature
            except Exception:
                LOG.exception("Firebase catalog state refresh failed")
            await asyncio.sleep(interval)

    def _next_helpful_message(
        self, messages: Sequence[str]
    ) -> tuple[str, dict] | None:
        current_messages = list(dict.fromkeys(messages))
        if not current_messages:
            return None
        current_set = set(current_messages)
        state = getattr(self, "helpful_message_cycle", {})
        raw_order = state.get("order", []) if isinstance(state, dict) else []
        if not isinstance(raw_order, list):
            raw_order = []
        try:
            raw_index = max(0, min(int(state.get("index", 0)), len(raw_order)))
        except (TypeError, ValueError):
            raw_index = 0

        shown: list[str] = []
        remaining: list[str] = []
        known: set[str] = set()
        for position, value in enumerate(raw_order):
            if not isinstance(value, str) or value not in current_set or value in known:
                continue
            known.add(value)
            if position < raw_index:
                shown.append(value)
            else:
                remaining.append(value)
        additions = [message for message in current_messages if message not in known]
        random.shuffle(additions)
        remaining.extend(additions)
        order = [*shown, *remaining]
        index = len(shown)
        last_shown = state.get("last_shown") if isinstance(state, dict) else None

        if index >= len(order):
            order = current_messages.copy()
            random.shuffle(order)
            if len(order) > 1 and order[0] == last_shown:
                order[0], order[1] = order[1], order[0]
            index = 0
        message = order[index]
        return message, {
            "version": 1,
            "order": order,
            "index": index + 1,
            "last_shown": message,
        }

    async def _announce_helpful_message_once(self) -> bool:
        activity_window = max(
            1.0,
            float(
                self.config.get(
                    "helpful_message_activity_window_seconds",
                    180,
                )
            ),
        )
        now = time.monotonic()
        active_human = any(
            player.connected
            and player.active
            and not player.is_ai
            and player.last_turn_monotonic is not None
            and now - player.last_turn_monotonic <= activity_window
            for player in self.players.values()
        )
        if not active_human:
            return False
        path = Path(
            self.config.get(
                "helpful_messages_file",
                "/etc/tronner-racing/helpful_messages.txt",
            )
        )
        messages = await asyncio.to_thread(load_helpful_messages, path)
        store = getattr(self, "store", None)
        if store is not None:
            messages.extend(load_custom_helpful_messages(store))
        selected = self._next_helpful_message(messages)
        if selected is None:
            return False
        message, next_cycle = selected
        await self.broadcast(style_tip_message(message))
        next_cycle["announced_round_token"] = getattr(
            self, "helpful_message_round_token", None
        )
        self.helpful_message_cycle = next_cycle
        if store is not None:
            store.set_json("helpful_message_cycle", next_cycle)
        return True

    def _cancel_helpful_message(self) -> None:
        self.helpful_message_round_generation = (
            getattr(self, "helpful_message_round_generation", 0) + 1
        )
        self.helpful_message_announced = False
        task = getattr(self, "_helpful_message_task", None)
        if task:
            task.cancel()
        self._helpful_message_task = None

    def _begin_helpful_message_round(self) -> None:
        map_key = self.current.key if self.current else "unknown"
        self.helpful_message_round_token = f"{map_key}:{time.time_ns()}"
        self.store.set_json(
            "helpful_message_round_token", self.helpful_message_round_token
        )
        self._schedule_helpful_message()

    def _schedule_helpful_message(self) -> None:
        self._cancel_helpful_message()
        if not self._round_is_active():
            return
        if not getattr(self, "helpful_message_round_token", None):
            map_key = self.current.key if getattr(self, "current", None) else "unknown"
            self.helpful_message_round_token = f"{map_key}:{time.time_ns()}"
            store = getattr(self, "store", None)
            if store is not None:
                store.set_json(
                    "helpful_message_round_token",
                    self.helpful_message_round_token,
                )
        if self.helpful_message_cycle.get("announced_round_token") == (
            self.helpful_message_round_token
        ):
            self.helpful_message_announced = True
            return
        generation = self.helpful_message_round_generation
        map_duration = max(
            0.0, float(self.config.get("map_duration_seconds", 300))
        )
        minimum = max(
            0.0,
            float(self.config.get("helpful_message_random_min_seconds", 30)),
        )
        maximum = max(
            0.0,
            float(
                self.config.get(
                    "helpful_message_random_max_seconds",
                    map_duration * 0.8,
                )
            ),
        )
        if self.deadline_epoch is not None:
            maximum = min(maximum, max(0.0, self.deadline_epoch - time.time() - 1))
        minimum = min(minimum, maximum)
        delay = random.uniform(minimum, maximum)
        self._helpful_message_task = asyncio.create_task(
            self._delayed_helpful_message(generation, delay),
            name="helpful-message",
        )

    async def _delayed_helpful_message(
        self, generation: int, delay: float
    ) -> None:
        try:
            await asyncio.sleep(max(0.0, delay))
            if (
                generation != self.helpful_message_round_generation
                or self.helpful_message_announced
                or not self._round_is_active()
                or self.transitioning
                or self.final_countdown_active
            ):
                return
            self.helpful_message_announced = True
            await self._announce_helpful_message_once()
        except asyncio.CancelledError:
            raise
        except Exception:
            LOG.exception("helpful console message announcement failed")
        finally:
            if self._helpful_message_task is asyncio.current_task():
                self._helpful_message_task = None

    async def helpful_message_announcer(self) -> None:
        if self._round_is_active() and self._helpful_message_task is None:
            self._schedule_helpful_message()
        await self.stop_event.wait()

    def _bootstrap_players_from_lines(
        self, lines: Sequence[str], authoritative: bool = False
    ) -> None:
        seen_players: set[int] = set()
        for line in lines:
            parts = line.split(maxsplit=5)
            if len(parts) < 6:
                continue
            player = self.player_for(parts[0])
            is_new = player is None
            was_connected = bool(player and player.connected)
            player = player or self.player_for(parts[0], create=True)
            assert player
            player.log_name = parts[0]
            # CYCLE_CREATED/CYCLE_DESTROYED and the ladderlog online-status
            # events are authoritative for players already being tracked. The
            # periodically rewritten online_players file can briefly lag those
            # events; allowing it to overwrite alive here can make a scheduled
            # respawn see a stale True value and silently abort. Only use the
            # file's alive bit when discovering or recovering a player.
            if is_new or not was_connected:
                player.alive = parts[1] == "1"
            player.connected = True
            if is_new:
                player.active = False
            player.display_name = parts[5]
            if "@" in parts[0]:
                player.auth_name = parts[0]
            self.register_alias(player, parts[0])
            seen_players.add(id(player))
            self.online_snapshot_misses.pop(id(player), None)

        if authoritative:
            for player in {id(item): item for item in self.players.values()}.values():
                if player.is_ai or id(player) in seen_players:
                    continue
                if not player.connected:
                    continue
                misses = self.online_snapshot_misses.get(id(player), 0) + 1
                self.online_snapshot_misses[id(player)] = misses
                if misses < 2:
                    continue
                player.connected = False
                player.active = False
                player.alive = False
                self.finalists.discard(id(player))
                self._cancel_player_freeze(player)
                self.command_windows.pop(id(player), None)
                self.command_warning_times.pop(id(player), None)

    async def bootstrap_players(self) -> None:
        path = Path(self.config.get("online_players_file", ""))
        while not self.stop_event.is_set():
            try:
                lines = self._decode_game_bytes(
                    path.read_bytes(),
                    "online player snapshot",
                ).splitlines()
                self._bootstrap_players_from_lines(lines[1:], authoritative=True)
            except (OSError, IndexError):
                pass
            await asyncio.sleep(2)

    async def follow_ladderlog(self) -> None:
        path = Path(self.config["ladderlog"])
        handle = None
        inode = None
        while not self.stop_event.is_set():
            try:
                stat = path.stat()
                if handle is None or inode != stat.st_ino or handle.tell() > stat.st_size:
                    if handle:
                        handle.close()
                    handle = path.open("rb")
                    handle.seek(0, os.SEEK_END)
                    inode = stat.st_ino
                    # Ask the native server to retransmit the current snapshot
                    # after this follower is positioned. This makes controller
                    # crashes/reloads safe even if the original snapshot event
                    # was only partially consumed.
                    await self.sink.send("CYCLE_REPLAY_SETTINGS_SNAPSHOT")
                raw_line = handle.readline()
                if raw_line:
                    if raw_line.startswith(b"ENCODING "):
                        fields = raw_line.strip().split()
                        if len(fields) >= 2:
                            with contextlib.suppress(UnicodeDecodeError):
                                self._apply_advertised_game_encoding(
                                    fields[1].decode("ascii")
                                )
                    await self.handle_line(
                        self._decode_game_bytes(raw_line, "ladderlog event")
                    )
                    continue
            except FileNotFoundError:
                pass
            await asyncio.sleep(0.05)
        if handle:
            handle.close()

    async def run(self) -> None:
        await self.initialize(start_http=True)
        loop = asyncio.get_running_loop()
        reload_signal_registered = False
        reload_ready_path: Path | None = None
        with contextlib.suppress(NotImplementedError, RuntimeError):
            loop.add_signal_handler(
                signal.SIGUSR1,
                self.request_controller_reload,
                "systemctl reload",
            )
            reload_signal_registered = True
        if reload_signal_registered:
            reload_ready_path = Path(
                self.config.get(
                    "controller_reload_ready_file",
                    "/run/tronner-racing/graceful-reload.pid",
                )
            )
            try:
                reload_ready_path.write_text(
                    f"{os.getpid()}\n", encoding="ascii"
                )
            except OSError:
                LOG.exception(
                    "unable to publish graceful reload readiness at %s",
                    reload_ready_path,
                )
        tasks = [
            asyncio.create_task(self.follow_ladderlog(), name="ladderlog"),
            asyncio.create_task(self.map_timer(), name="map-timer"),
            asyncio.create_task(self.repository_refresher(), name="repository-refresh"),
            asyncio.create_task(self.catalog_state_monitor(), name="catalog-state"),
            asyncio.create_task(
                self.reconcile_map_reviews_once(), name="map-review-reconciliation"
            ),
            asyncio.create_task(self.bootstrap_players(), name="player-bootstrap"),
            asyncio.create_task(
                self.helpful_message_announcer(),
                name="helpful-message-announcer",
            ),
            asyncio.create_task(
                self.server_options_refresher(),
                name="server-options-refresher",
            ),
            asyncio.create_task(
                self.player_activity_monitor(),
                name="player-activity-monitor",
            ),
            asyncio.create_task(
                self.live_dashboard_publisher(),
                name="live-dashboard",
            ),
            asyncio.create_task(
                self.server_management_worker(),
                name="server-management",
            ),
            asyncio.create_task(
                self.website_rating_worker(),
                name="website-rating",
            ),
            asyncio.create_task(
                self.follow_server_console(),
                name="server-console",
            ),
        ]
        try:
            await self.stop_event.wait()
        finally:
            for task in tasks:
                task.cancel()
            await asyncio.gather(*tasks, return_exceptions=True)
            if reload_signal_registered:
                loop.remove_signal_handler(signal.SIGUSR1)
            if reload_ready_path is not None:
                with contextlib.suppress(OSError):
                    if reload_ready_path.read_text(encoding="ascii").strip() == str(
                        os.getpid()
                    ):
                        reload_ready_path.unlink()
            self.close()


def load_config(path: Path) -> dict:
    with path.open("r", encoding="utf-8") as handle:
        return json.load(handle)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Tronner Racing server script")
    parser.add_argument("--config", type=Path, required=True)
    parser.add_argument("--check", action="store_true", help="sync and validate maps, then exit")
    return parser.parse_args()


async def async_main() -> int:
    args = parse_args()
    config = load_config(args.config)
    controller = TronnerRacing(config)
    if args.check:
        try:
            await controller.initialize(start_http=False)
            print(
                json.dumps(
                    {
                        "maps": len(controller.repository.catalog),
                        "skipped": controller.repository.issues,
                        "spawn_points": sum(
                            len(entry.spawns) for entry in controller.repository.catalog.values()
                        ),
                    },
                    indent=2,
                )
            )
            return 0
        finally:
            controller.close()
    await controller.run()
    return 0


def main() -> int:
    logging.basicConfig(
        level=os.environ.get("TRONNER_RACING_LOG_LEVEL", "INFO"),
        format="%(asctime)s %(levelname)s %(name)s: %(message)s",
    )
    try:
        return asyncio.run(async_main())
    except KeyboardInterrupt:
        return 130


if __name__ == "__main__":
    raise SystemExit(main())
