COQOPTS = -R ./ MetaCoq.VerifiedExtraction.Benchmarks -R lib MetaCoq.VerifiedExtraction.Benchmarks.lib

# Names of the benchmarks
TESTS=$(shell cat TESTS)

all: lib tests

.PHONY: all default clean lib cleanlib tests run copy $(TESTS)

.SILENT: lib

lib: 
	@make -C lib > /dev/null 2>&1

cleanlib:
	$(MAKE) clean -C lib

tests: lib
	@make -C ocaml all
	@make -C ocaml-noopt all
	@make -C malfunction all
	@make -C malfunction-o2 all
	# $(MAKE) -C malfunction-verified all

run:
	$(MAKE) -C ocaml run
	$(MAKE) -C ocaml-noopt run
	$(MAKE) -C malfunction run
	$(MAKE) -C malfunction-o2 run
	# $(MAKE) -C malfunction-verified run

