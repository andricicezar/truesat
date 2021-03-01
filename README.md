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
You can download test files from this [website](https://www.cs.ubc.ca/~hoos/SATLIB/benchm.html).

### Running
Any of the 3 solvers accept only one argument, which is the path
to the test.
```
./main.exe benchmarks/hole6.cnf
```

### Benchmarks
The folder `bench_exec_configs` contains the configuration files
we used to run the benchmarks. Please check the [documentation of the tool `bench-exec`](https://github.com/sosy-lab/benchexec)
to see how to reproduce them.


### Contributors
* Cezar C. Andrici, Alexandru Ioan Cuza University of Iasi, Romania
* Stefan Ciobaca, Alexandru Ioan Cuza University of Iasi, Romania

