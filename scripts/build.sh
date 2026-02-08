#!/usr/bin/env bash
set -euo pipefail

target="${1:-release}"

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
build_dir="$root/build"
cc="${CC:-cc}"

mkdir -p "$build_dir"

case "$target" in
  release)
    "$cc" -Os "$root/l.c" -o "$build_dir/l_lin"
    printf 'Built %s\n' "$build_dir/l_lin"
    ;;
  asan)
    "$cc" -fsanitize=address "$root/l.c" -o "$build_dir/l_lin_asan"
    printf 'Built %s\n' "$build_dir/l_lin_asan"
    ;;
  clean)
    rm -rf "$build_dir"
    printf 'Cleaned %s\n' "$build_dir"
    ;;
  *)
    echo "Usage: $0 {release|asan|clean}" >&2
    exit 2
    ;;
esac

