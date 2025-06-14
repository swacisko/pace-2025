# PACE 2025 submission

# Dominating set solver

# Hitting set solver

***

Solver for the dominating set problem and hitting set problem, written as an entry to the [PACE 2025 challenge](https://pacechallenge.org/).
This repository contains code of an exact solver and a heuristic solver.

***

**Requirements**:

CMake VERSION 3.15 or higher<br>
c++ 20 or higher<br>
python ortools module with CPSAT solver (use, e.g., ``python3 -m pip install -U --user ortools'')

***

**Installation**:


Use cmake to obtain a binary file, e.g. in linux in the main directory (pace-2025) you can use the following commands:

mkdir build<br>
cp solveCPSAT.py build/solveCPSAT.py<br>
cd build<br>
cmake ..<br>
make <br>
<br>
After this, the executable files named should be in the "build" directory.


***

**Usage:**

./solver_executable < example_input.gr > example_output.out

Heuristic solvers will be run by default for 290 seconds (possibly with some slight overhead for very large instances, needed to terminate computation and print result).

<br>
