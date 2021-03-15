download_tests:
	python3 download-tests.py
	chmod -R 755 tests

bench_truesat:
	benchexec truesat.xml --tool-directory /home/cezar/work/fii/truesat/truesat_src

bench_cpp:
	benchexec cpp.xml --tool-directory /home/cezar/work/fii/truesat

bench_cs:
	benchexec cs.xml --tool-directory /home/cezar/work/fii/truesat/csharp_solver

bench_truesat_bigints:
	benchexec truesat-bigints.xml --tool-directory /home/cezar/work/fii/truesat/truesat_bigints

bench_isasat:
	benchexec isasat.xml --tool-directory /home/cezar/work/fii/isafol-clone

bench_kissat:
	benchexec kissat.xml --tool-directory /home/cezar/work/fii/kissat

bench_minisat:
	benchexec minisat.xml --tool-directory /home/cezar/work/fii/minisat
