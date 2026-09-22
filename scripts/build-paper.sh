#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
build_dir="$(mktemp -d "${TMPDIR:-/tmp}/prelol-paper.XXXXXX")"
trap 'rm -rf -- "$build_dir"' EXIT

cd "$repo_root"
latexmk -silent -pdf -interaction=nonstopmode -halt-on-error \
  -outdir="$build_dir" paper/main.tex
cp "$build_dir/main.pdf" paper/main.pdf
printf 'Built paper/main.pdf\n'
