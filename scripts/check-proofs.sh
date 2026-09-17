#!/usr/bin/env bash
set -euo pipefail

build_dir="$(mktemp -d)"
trap 'rm -rf "$build_dir"' EXIT

coqc -q -noglob -o "$build_dir/ite.vo" 1/ite.v
coqc -q -noglob -o "$build_dir/prg.vo" 2/prg.v

for source in examples/eloadas_01/*.v; do
  output_name="$(basename "${source%.v}").vo"
  coqc -q -noglob -o "$build_dir/$output_name" "$source"
done

mkdir -p "$build_dir/eloadas_02"
for source in examples/eloadas_02/*.v; do
  # A practice_* fájlok szándékosan Abort.-tal zárt kezdőfeladatok:
  # ezeknél a definíciók és a tétel állításának típushelyességét ellenőrizzük.
  output_name="$(basename "${source%.v}").vo"
  coqc -q -noglob -o "$build_dir/eloadas_02/$output_name" "$source"
done
