#!/bin/sh
set -eu

cd "$(dirname "$0")/.."

# Give the tracked artifacts a stable timestamp.
export SOURCE_DATE_EPOCH=1784851200
export FORCE_SOURCE_DATE=1

pandoc paper/Dean_conjecture_k5.md --standalone \
  -o paper/Dean_conjecture_k5.tex

pandoc paper/Dean_conjecture_k5.md --pdf-engine=xelatex \
  -o paper/Dean_conjecture_k5.pdf
