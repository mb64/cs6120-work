#!/bin/bash
# Simple test: run the program on an input .bril file supplied in the command line

one_test() {
  f="$1"
  basename="$(basename "$f")"
  ARGS=`sed -ne 's/.*ARGS: \(.*\)/\1/p' "$f"`
  echo "$basename"
  diff <(cat "$f" | bril2json | cabal run | brili $ARGS) <(cat "$f" | bril2json | brili $ARGS) || echo "$basename: FAILED"
}

one_arg() {
  if [ $RECURSIVE -eq 1 ] ; then
    find "$1" -type f -name '*.bril' | while read f; do one_test "$f" ; done
  elif [ -f "$1" ] ; then
    one_test "$1"
  else
    for f in "$1"/*.bril ; do one_test "$f" ; done
  fi
}

if [ $# -eq 0 ] ; then
  echo "Usage: $0 [-r] test..."
  echo "  test: a .bril file or directory of .bril files"
  echo "  -r: recursively process subdirectories"
  exit 1
fi

RECURSIVE=0
if [ "$1" = "-r" ] ; then
  RECURSIVE=1
  shift
fi

for arg in "$@" ; do one_arg "$arg" ; done

