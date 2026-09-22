#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
build_dir="$(mktemp -d "${TMPDIR:-/tmp}/relol-study.XXXXXX")"
trap 'rm -rf -- "$build_dir"' EXIT

cd "$repo_root"
latexmk -silent -pdf -interaction=nonstopmode -halt-on-error \
  -outdir="$build_dir" docs/study/rules.tex
cp "$build_dir/rules.pdf" docs/study/rules.pdf
printf 'Built docs/study/rules.pdf\n'
