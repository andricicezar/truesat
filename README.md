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
or use our script `bench/download-tests.py`.

### Running
Any of the 3 solvers accept only one argument, which is the path
to the test.
```
./main.exe bench/tests/...
```

### Benchmarks
We used the tool [`bench-exec`](https://github.com/sosy-lab/benchexec) to run our benchmarks.

#### Instalation
Please check the [documentation of `bench-exec`](https://github.com/sosy-lab/benchexec)
to see how to install it.

#### Prepare
1. Compile any of the solvers you would like to bench.
2. Go into the `bench/truesat-bench` and run the command:
`python3 -m pip install . --upgrade`.
3. In the `bench` folder run `python3 download-tests.py`.

#### Running tests
You can run the benchmarks for the dafny solver by using the make command.
Please open it, and fix the paths to the solvers. After that, you can run
`make bench_truesat`.

### Contributors
* Cezar C. Andrici, Alexandru Ioan Cuza University of Iasi, Romania
* Stefan Ciobaca, Alexandru Ioan Cuza University of Iasi, Romania

