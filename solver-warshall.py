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

    def __init__(self, optimize):
        self.optimize = optimize

    def solve(self, p):
        print("(set-option :print-success false)")
        print("(set-logic QF_UFLIA)")

        # Numbers in cells
        print("(declare-fun n (Int) Int)")
        
        # Fill in the initially known numbers
        for (a,b,k) in p.nums:
            x = a * p.cols + b
            print("(assert (= (n {}) {}))".format(x,k))
        
        # Denotes whether at stage t cells x and y are connected
        print("(declare-fun c (Int Int Int) Bool)")
        
        # Set initial connections
        for (i1,j1,i2,j2) in product(xrange(p.rows), xrange(p.cols),
                                     xrange(p.rows), xrange(p.cols)):
            x = i1 * p.cols + j1
            y = i2 * p.cols + j2
            if x == y:
                print("(assert (c 0 {} {}))".format(x,y))
            elif abs(i1 - i2) + abs(j1 - j2) == 1:
                print("(assert (= (c 0 {0} {1}) (= (n {0}) (n {1}))))".format(x,y))
            else:
                print("(assert (not (c 0 {} {})))".format(x,y))
        
        # Apply Warshall's algorithm
        for (i3,j3) in product(xrange(p.rows), xrange(p.cols)):
            z = i3 * p.cols + j3
            for (i1,j1,i2,j2) in product(xrange(p.rows), xrange(p.cols),
                                         xrange(p.rows), xrange(p.cols)):
                x = i1 * p.cols + j1
                y = i2 * p.cols + j2
                print("(assert (= (c {} {} {})".format(z+1,x,y))
                print("           (or (c {0} {1} {2}) (and (c {0} {1} {0}) (c {0} {0} {2})))))".format(z,x,y))

        # Connected cells must have the same number in them
        z = p.rows * p.cols
        for (i1,j1,i2,j2) in product(xrange(p.rows), xrange(p.cols),
                                     xrange(p.rows), xrange(p.cols)):
            x = i1 * p.cols + j1
            y = i2 * p.cols + j2
            print("(assert (=> (c {0} {1} {2}) (= (n {1}) (n {2}))))".format(z,x,y))

        # Assert the sizes of the polyominos
        z = p.rows * p.cols
        for (i1,j1) in product(xrange(p.rows), xrange(p.cols)):
            x = i1 * p.cols + j1
            print("(assert (= (+")
            for (i2,j2) in product(xrange(p.rows), xrange(p.cols)):
                y = i2 * p.cols + j2
                print("              (ite (c {} {} {}) 1 0)".format(z,x,y))
            print(") (n {})))".format(x))

        # Optimization 
        # Doing this just for the last costs 45 seconds more for p7
        if self.optimize:
            for z in xrange(p.rows * p.cols + 1):
                for (i1,j1,i2,j2) in product(xrange(p.rows), xrange(p.cols),
                                             xrange(p.rows), xrange(p.cols)):
                    x = i1 * p.cols + j1
                    y = i2 * p.cols + j2
                    d = abs(i1 - i2) + abs(j1 - j2)
                    print("(assert (=> (>= {} (n {}))".format(d,x))
                    print("            (not (c {} {} {}))))".format(z,x,y))

        print("(check-sat)")
        
        # Print result
        for (i,j) in product(xrange(p.rows), xrange(p.cols)):
            x = i * p.cols + j
            print("(get-value ((n {})))".format(x))


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
