#!/usr/bin/env bash
set -euo pipefail

repository_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
source_dir=${TRONNER_ENGINE_SOURCE_DIR:?Set TRONNER_ENGINE_SOURCE_DIR to the patched engine source tree.}
build_dir=${TRONNER_ENGINE_BUILD_DIR:?Set TRONNER_ENGINE_BUILD_DIR to its completed build tree.}
output_dir=${SMOKE_PROBE_DIR:-$build_dir/tronner-smoke-probes}

test -f "$source_dir/src/tron/gGame.cpp"
test -f "$build_dir/config.h"
for library in libtron libenginecore libengine libnetwork libui librender libtools; do
    test -f "$build_dir/src/$library.a"
done

read_make_flags() {
    local variable=$1
    python3 - "$build_dir/src/Makefile" "$variable" <<'PY'
import pathlib
import shlex
import sys

prefix = sys.argv[2] + " ="
for line in pathlib.Path(sys.argv[1]).read_text(encoding="utf-8").splitlines():
    if line.startswith(prefix):
        for value in shlex.split(line.split("=", 1)[1].strip()):
            print(value)
        break
PY
}

mapfile -t zthread_cxxflags < <(read_make_flags ZTHREAD_CXXFLAGS)
mapfile -t zthread_libs < <(read_make_flags ZTHREAD_LIBS)

mkdir -p "$output_dir"
for probe in network_hold server_info_probe start_cycle_test; do
    g++ -std=c++11 -O2 -Wl,--allow-multiple-definition \
        -I"$build_dir" -I"$build_dir/src" \
        -iquote "$source_dir/src" \
        -iquote "$source_dir/src/tools" \
        -iquote "$source_dir/src/network" \
        -iquote "$source_dir/src/engine" \
        -iquote "$source_dir/src/tron" \
        -iquote "$source_dir/src/ui" \
        -iquote "$source_dir/src/render" \
        "${zthread_cxxflags[@]}" \
        $(pkg-config --cflags libxml-2.0) \
        "$repository_dir/deploy/smoke/$probe.cpp" \
        -Wl,--start-group \
        "$build_dir/src/libtron.a" \
        "$build_dir/src/libenginecore.a" \
        "$build_dir/src/libengine.a" \
        "$build_dir/src/libnetwork.a" \
        "$build_dir/src/libui.a" \
        "$build_dir/src/librender.a" \
        "$build_dir/src/libtools.a" \
        -Wl,--end-group \
        "${zthread_libs[@]}" \
        $(pkg-config --libs libxml-2.0) -lpthread -lm -lz \
        -o "$output_dir/$probe"
done

printf 'built disposable smoke probes in %s\n' "$output_dir"
