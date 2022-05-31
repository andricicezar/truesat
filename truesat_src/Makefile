verify:
	dafny /compile:0 /vcsCores:8 /errorLimit:1 /trace *.dfy solver/*.dfy

build:
	dafny /compileTarget:cs /spillTargetCode:1 /compile:2 truesat.dfy file_input.cs

clean:
	rm -f *.dll solver/*.dll *.dll.mdb solver/*.dll.mdb truesat.cs truesat.exe.mdb
