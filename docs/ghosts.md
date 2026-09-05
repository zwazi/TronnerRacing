# Private replay ghosts

`/ghost` selects a recorded run to compare against on the current map:

```text
/ghost
/ghost pb
/ghost wr
/ghost rank 5
/ghost player Alice
/ghost off
```

`/ghost` defaults to PB. PB uses the requester's best finish. Before their first
finish, it uses the unfinished replay that came closest to the winzone according
to the route-progress field, replacing it whenever a later attempt gets closer.
Once the player finishes, unfinished attempts are no longer PB candidates. WR
uses rank 1, and rank/name selectors use the current map's leaderboard. PB and
rank-number preferences persist between rounds and reconnects until replaced or
disabled with `/ghost off`; they are resolved against each new map before the
player's next spawn. WR and named-player selections apply only to the current
round.

The controller prefers the exact replay for a selected leaderboard time. If that
time predates input capture, it uses the player's fastest available full-run
replay and states both the replay and ranked times in the confirmation. When a
new run changes an active PB, WR, rank, or named-player selection, the controller
reloads that selection for the requester and uses the updated ghost on their
next attempt.

Historical resource names and revisions remain eligible. A strict XML and
settings comparison is used to choose the verified coordinate conversion when
possible, including `SIZE_FACTOR` normalization for maps migrated from scaled to
baked coordinates. If geometry or historical server settings cannot be proven
identical, the replay is still loaded with a best-effort size conversion instead
of being rejected. Only a missing or structurally invalid full-run input stream
prevents loading.

Physics compatibility compares the captured setting values, not only the raw
snapshot identifier. Runtime-only `SERVER_OPTIONS` text and
`PING_CHARITY_SERVER` latency allowance are ignored because they cannot affect
the route of a server-driven, non-colliding ghost. Other differences are logged
for diagnosis but no longer block playback.

The controller writes a bounded, mode-0600 one-shot plan under
`/var/lib/armagetronad/ghosts`. The patched server creates an invulnerable,
server-driven cycle, replays accepted turn and brake inputs at their recorded
microsecond offsets, and starts from the human cycle's authoritative release
time. Teleport, speed, and rubber zones still affect playback so the recorded
route remains faithful. Ghosts do not create walls, affect other cycles,
trigger scoring/death/checkpoint zones, or enter racing ladder logs.

Newly recorded replays also store the authoritative position, direction, speed,
and turn count after every accepted turn. The server applies these turn
keyframes after the recorded input and clears the ordinary delayed-input queue,
preventing simulation drift near walls and preventing a queued turn from firing
later as an apparent extra input. Version-1 plans and older runs without turn
keyframes remain supported as best-effort input-only replays.

Replay plans store positions in map coordinates. The server converts those
positions through the arena size multiplier when it creates the ghost, matching
the normal player spawn path on both size-zero and resized maps.

Administrators can recover start fields written by older controller versions
from retained authoritative ladder logs. The repair defaults to a dry run,
requires a new integrity-checked database backup for `--apply`, and skips every
ambiguous match:

```sh
python3 tools/repair_replay_starts.py \
  --database /var/lib/tronner-racing/TronnerRacing.sqlite3 \
  --ladderlog /var/lib/armagetronad/ladderlog.txt
```

## Legacy client compatibility

No new network descriptor or client feature is required. The ghost is sent as
the existing player descriptor 201 and cycle descriptor 320 used by unmodified
0.2.8 clients. A wire-only negative cycle distance prevents legacy clients from
predicting a wall for the ghost. Because 0.2.8 has no translucent-cycle protocol,
the compatibility rendering is an ordinary cyan cycle named for the selected
player. A player's own PB ghost is named `PB`; other ghosts use only the replay
player's name. Names are converted to ASCII and truncated as needed to at most
15 visible bytes, the safe limit for 0.2.8's 16-character NUL-terminated
player-name storage.

Visibility is filtered per network connection. Other clients receive neither
the ghost player nor its cycle. Multiple local players using one split-screen
connection necessarily share that connection's view, which is a limitation of
the legacy protocol.
