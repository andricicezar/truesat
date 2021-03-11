start:
	python3 download-tests.py
	chmod -R 755 tests

bench_truesat:
	benchexec truesat.xml --tool-directory /home/cezar/work/fii/truesat/truesat_src  

bench_truesat_bigints:
	benchexec truesat-bigints.xml --tool-directory /home/cezar/work/fii/truesat/truesat_bigints

bench_isasat:
	benchexec isasat.xml --tool-directory /home/cezar/work/fii/isafol-clone

bench_kissat:
	benchexec kissat.xml --tool-directory /home/cezar/work/fii/kissat

bench_minisat:
	benchexec minisat.xml --tool-directory /home/cezar/work/fii/minisat

bench: bench_truesat bench_isasat
