#!/usr/bin/env bash
set -euo pipefail

build_dir="$(mktemp -d)"
trap 'rm -rf "$build_dir"' EXIT

coqc -q -noglob -o "$build_dir/ite.vo" 1/ite.v

for source in examples/eloadas_01/*.v; do
  output_name="$(basename "${source%.v}").vo"
  coqc -q -noglob -o "$build_dir/$output_name" "$source"
done
