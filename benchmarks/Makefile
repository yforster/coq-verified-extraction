COQOPTS = -R ./ MetaCoq.VerifiedExtraction.Benchmarks -R lib MetaCoq.VerifiedExtraction.Benchmarks.lib

# Names of the benchmarks
TESTS=$(shell cat TESTS)

all: lib tests run

.PHONY: all default clean lib cleanlib tests run copy $(TESTS)

lib/Makefile:
	cd lib; coq_makefile -f _CoqProject -o Makefile

lib: lib/Makefile
	$(MAKE) -C lib

cleanlib:
	$(MAKE) clean -C lib

tests: lib
	$(MAKE) -C lib 
	$(MAKE) -C ocaml all
	$(MAKE) -C malfunction all

run:
	$(MAKE) -C ocaml run
	$(MAKE) -C malfunction run
