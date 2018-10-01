# SMT Fillomino Solvers

This repository contains two SMT-based solvers for the puzzle Fillomino.
One of the main difficulties in solving Fillomino puzzles using a SMT solver
is determining which grid cells belong to the same polyomino.
The two solvers in this repo solve this problem in two different ways.
The first solver constructs a spanning tree for each polyomino,
and the second solver uses a SAT-implementation of Warshall's algorithm.

## Usage

The first step is to convert the Fillomino puzzle to a SMT-LIBv2 file.
```
python2 solver-tree.py problems/p0.fillomino > p0.fillomino.smt2
```

The resulting file can then be used with any SMT solver which SMT-LIBv2 files,
such as Yices or Z3.
