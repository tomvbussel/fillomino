from argparse import ArgumentParser
from datetime import datetime
from itertools import product
from os.path import split



class Fillomino(object):
    def __init__(self, rows, cols, nums):
        self.rows = rows
        self.cols = cols
        self.nums = nums


class FillominoSolver(object):
    """A Fillomino Solver using SMT."""

    def __init__(self, optimize=False):
        self.optimize = optimize

    def adj(self, i, j):
        l = []
        if i-1 >= 0:
            l.append((i-1,j))
        if i+1 < self.rows:
            l.append((i+1,j))
        if j-1 >= 0:
            l.append((i,j-1))
        if j+1 < self.cols:
            l.append((i,j+1))
        return l

    def solve(self, p):
        print("(set-option :print-success false)")
        print("(set-logic QF_UFLIA)")

        self.rows = p.rows
        self.cols = p.cols
        
        # Directed edges
        e = {}
        for (i1,j1) in product(xrange(p.rows), xrange(p.cols)):
            x = i1 * p.cols + j1
            for (i2,j2) in self.adj(i1,j1):
                y = i2 * p.cols + j2
                print("(declare-fun e_{}_{} () Int)".format(x,y))
                print("(assert (or (= e_{0}_{1} 0) (= e_{0}_{1} 1)))".format(x,y))

        # Tree 1: edges only in one direction
        for (i1,j1) in product(xrange(p.rows), xrange(p.cols)):
            x = i1 * p.cols + j1
            for (i2,j2) in self.adj(i1,j1):
                y = i2 * p.cols + j2
                print("(assert (<= (+ e_{0}_{1} e_{1}_{0}) 1))".format(x,y))

        # Tree 2: each cell has at most one parent
        for (i1,j1) in product(xrange(p.rows), xrange(p.cols)):
            x = i1 * p.cols + j1
            print("(assert (<= (+")
            for (i2,j2) in self.adj(i1,j1):
                y = i2 * p.cols + j2
                print("               e_{}_{}".format(y,x))
            print(") 1))")

        # Number in cell
        for (i1,j1) in product(xrange(p.rows), xrange(p.cols)):
            x = i1 * p.cols + j1
            print("(declare-fun n_{} () Int)".format(x))
    
        # Initial numbers in cell
        for (i,j,k) in p.nums:
            x = i * p.cols + j
            print("(assert (= n_{} {}))".format(x,k))
        
        # Size of cell
        for (i1,j1) in product(xrange(p.rows), xrange(p.cols)):
            x = i1 * p.cols + j1
            print("(declare-fun s_{} () Int)".format(x))

        # Calculate size of cell as 1 + size of children
        for (i1,j1) in product(xrange(p.rows), xrange(p.cols)):
            x = i1 * p.cols + j1
            print("(assert (= s_{} (+ 1".format(x))
            for (i2,j2) in self.adj(i1,j1):
                y = i2 * p.cols + j2
                print("                   (ite (= e_{0}_{1} 1) s_{1} 0)".format(x,y))
            print(")))")

        # For roots size of cell must be equal to number in cell
        for (i1,j1) in product(xrange(p.rows), xrange(p.cols)):
            x = i1 * p.cols + j1
            print("(assert (=> (= (+")
            for (i2,j2) in self.adj(i1,j1):
                y = i2 * p.cols + j2
                print("                  e_{}_{}".format(y,x))
            print(") 0) (= s_{0} n_{0})))".format(x))

        # Number of children is equal to number of parent
        for (i1,j1) in product(xrange(p.rows), xrange(p.cols)):
            x = i1 * p.cols + j1
            for (i2,j2) in self.adj(i1,j1):
                y = i2 * p.cols + j2
                print("(assert (=> (= e_{0}_{1} 1) (= n_{0} n_{1})))".format(x,y))
    
        # Root of corresponding tree
        for (i1,j1) in product(xrange(p.rows), xrange(p.cols)):
            x = i1 * p.cols + j1
            print("(declare-fun r_{} () Int)".format(x))
        
        # Roots
        for (i1,j1) in product(xrange(p.rows), xrange(p.cols)):
            x = i1 * p.cols + j1
            print("(assert (=> (= (+")
            for (i2,j2) in self.adj(i1,j1):
                y = i2 * p.cols + j2
                print("                  e_{}_{}".format(y,x))
            print(") 0) (= r_{0} {0})))".format(x))

        # Neighboring cells with same number must be in same area
        for (i1,j1) in product(xrange(p.rows), xrange(p.cols)):
            x = i1 * p.cols + j1
            for (i2,j2) in self.adj(i1,j1):
                y = i2 * p.cols + j2
                print("(assert (=> (= n_{0} n_{1}) (= r_{0} r_{1})))".format(x,y))

        print("(check-sat)")
        
        # Print result
        for (i,j) in product(xrange(p.rows), xrange(p.cols)):
            x = i * p.cols + j
            print("(get-value (n_{}))".format(x))


def read_constraints(fname):
    def reader(fname):
        with open(fname, "r") as f:
            for line in f:
                r = line.split()
                for x in r:
                    yield x
    r = reader(fname)

    rows = int(next(r))
    cols = int(next(r))
    
    nums = []
    for (i,j) in product(xrange(rows), xrange(cols)):
        v = next(r)
        if v.isdigit():
            nums.append((i,j,int(v)))

    return Fillomino(rows=rows, cols=cols, nums=nums)


def main():
    parser = ArgumentParser(description="Fillomino solver using SMT.")

    parser.add_argument("problem", metavar="filename", type=str,
                        help="the Fillomino problem to solve")

    parser.add_argument("--optimize", "-o", action="store_true",
                        help="add extra optimization")

    args = parser.parse_args()

    fillomino = FillominoSolver(args.optimize)

    if args.problem:
        puzzle = read_constraints(args.problem)
        fillomino.solve(puzzle)
    else:
        print("No problem specified")



if __name__ == "__main__":
    main()
