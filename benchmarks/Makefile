COQOPTS = -R ./ MetaCoq.VerifiedExtraction.Benchmarks -R lib MetaCoq.VerifiedExtraction.Benchmarks.lib

# Names of the benchmarks
TESTS=$(shell cat TESTS)

all: lib tests exec run

.PHONY: all default clean lib cleanlib tests run copy $(TESTS)

lib/Makefile:
	cd lib; coq_makefile -f _CoqProject -o Makefile

lib: lib/Makefile
	$(MAKE) -C lib

cleanlib:
	$(MAKE) clean -C lib

tests: tests.v
	coqc $(COQOPTS) tests.v
