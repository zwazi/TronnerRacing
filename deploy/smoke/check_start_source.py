"""Guard the applied source, not the contents of superseded patch layers."""
import pathlib
import sys

source = (pathlib.Path(sys.argv[1]) / "src/tron/gCycle.cpp").read_text()
for function in ("StartBraked", "OnBrakeStateChanged"):
    start = source.index(f"void gCycle::{function}(")
    opening = source.index("{", start)
    depth = 1
    end = opening + 1
    while depth:
        depth += (source[end] == "{") - (source[end] == "}")
        end += 1
    body = source[opening:end]
    for forbidden in (
        "ClientZeroAcceleration",
        "CYCLE_SPEED_DECAY_BELOW",
    ):
        if forbidden in body:
            raise SystemExit(f"{function} must not override client race physics: {forbidden}")
print("Applied start/release source has no decay override")
