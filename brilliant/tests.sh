#!/bin/bash
# Simple test: run the program on an input .bril file supplied in the command line

one_test() {
  f="$1"
  basename="$(basename "$f")"
  ARGS=`sed -ne 's/.*ARGS: \(.*\)/\1/p' "$f"`
  echo "$basename"
  before=`mktemp`
  after=`mktemp`
  diff -y <(cat "$f" | bril2json | brili -p $ARGS 2>$before ) <(cat "$f" | bril2json | cabal run -v0 | brili -p $ARGS 2>$after ) || echo "$basename: FAILED"
  before_count=$(cat $before | sed -ne 's/total_dyn_inst: \(.*\)/\1/p')
  after_count=$(cat $after | sed -ne 's/total_dyn_inst: \(.*\)/\1/p')
  if [ $before_count -lt $after_count ] ; then
    echo "$basename: REGRESSION: $before_count to $after_count"
  fi
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

