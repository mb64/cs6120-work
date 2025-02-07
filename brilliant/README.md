# Simple compiler

Does LVN and trivial DCE. In addition, it does DCE using CFG reachability,
finds a static-instruction-count-optimal basic block layout, and does very
simple peephole optimization.

I've been testing with `./tests.sh path/to/bril/benchmarks/core` which tests
that the optimizations preserve behavior on all core benchmarks, and that they
do not increase dynamic instruction count.

