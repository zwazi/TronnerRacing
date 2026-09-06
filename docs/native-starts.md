# Native brake starts

Brake/countdown starts use the ordinary synchronized cycle brake, plus an
authoritative stationary hold on the server. They must not send a per-client
`CYCLE_SPEED_DECAY_BELOW` override or change global race acceleration. Normal
physics configuration remains unchanged: zeroing that global setting disables
normal below-base-speed acceleration and changes recorded routes.

Stock clients report brake state, not physical key presses. A toggle-brake
press releases the brake; a continuous-brake binding releases on key-up (tap
the key). Brake-off is confirmed for at least 250 ms, increased with measured
lag up to one second, because older clients clear keys before sending their
chat/away state. Chat/away cancels a pending release. Countdown starts ignore
manual brake input and release on their scheduled simulation timestamp.

The release restores the native spawn/checkpoint speed. The existing release
event is the common origin for race timing, replay capture, ghosts and private
zone growth. Held turns retain shortest-net-rotation counting.

No replay schema, ghost plan version, compatibility filter, stored recording,
or normal racing movement formula changes. Historical ghosts remain eligible.

`deploy/build_engine.sh` runs the actual brake-input helper tests. The Engine
workflow also links a headless fixture against the built engine to exercise
real cycle holding, held turns, countdown release and manual/focus handling.
This does not replace interactive testing on each stock client family.
