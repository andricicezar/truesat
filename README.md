# Who Verifies the Verifiers? A Computer-Checked Implementation of the DPLL Algorithm in Dafny

This repository contain 3 DPLL solvers done in Dafny, C++ and C#. 

### Requirements
Dafny 2.3.0.10506
csc version: 3.100.19.26603 (9d80dea7)
gcc version: 9.1.0

### Build
In any of the 3 folders, there is a `Makefile` which contains
how to build the binaries. Just run the `make` command.

### Download tests
You can download test files from this [website](https://www.cs.ubc.ca/~hoos/SATLIB/benchm.html)
or use our script `bench_exec_configs/bench/download-tests.py`.

### Running
Any of the 3 solvers accept only one argument, which is the path
to the test.
```
./main.exe benchmarks/hole6.cnf
```

### Benchmarks
We used the tool [`bench-exec`](https://github.com/sosy-lab/benchexec) to run our benchmarks.

#### Instalation
Please check the [documentation of `bench-exec`](https://github.com/sosy-lab/benchexec)
to see how to install it.

#### Prepare
1. Set `TRUESAT_BENCHEXEC` to the root of the TrueSAT project. You can run `export 
TRUESAT_BENCHEXEC=$(pwd)` in this folder.
2. Go into the `bench_exec_configs/package_bench` and run the command:
`python3 -m pip install . --upgrade`.
3. Go into `bench_exec_configs/bench` and run `python3 download-tests.py`.
4. The solvers must be compiled to be able to run the benchmarks, therefore make sure
you built the solvers.

#### Running tests
You can run the benchmarks for the dafny solver by running the command
 `benchexec test-dpllsolver.py` in the folder `bench_exec_configs/bench`.

### Contributors
* Cezar C. Andrici, Alexandru Ioan Cuza University of Iasi, Romania
* Stefan Ciobaca, Alexandru Ioan Cuza University of Iasi, Romania

