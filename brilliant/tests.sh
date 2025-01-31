#!/bin/sh
# Simple test: run the program on an input .bril file supplied in the command line

die() {
  echo "$@" >&2
  exit 1
}

cat "$1" | bril2json | cabal run && echo "Success!" || die "Test failed! See above output"

