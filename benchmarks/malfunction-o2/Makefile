COQOPTS = -R ../lib MetaCoq.VerifiedExtraction.Benchmarks.lib -w -extraction-opaque-accessed,-notation-overridden,-opaque-let
CCOMPILER=gcc

# Names of the benchmarks
TESTS=$(shell cat TESTS)
# Names of the generated cfiles
MLFFILES=$(patsubst %,%.mlf, $(TESTS))
MLIFILES=$(patsubst %,%.mli, $(TESTS))
CMXFILES=$(patsubst %,%.cmx, $(TESTS))

default: tests run
all: tests mainopt run

.PHONY: run clean cleanml

$(MLFILES): tests
$(CMXFILES): $(TESTS)
exec: $(TESTS)

clean:
	rm -f ./*.cmi
	rm -f ./*.cmo
	rm -f ./*.cmx
	rm -f ./*.cma
	rm -f ./*.o
	rm -f $(TESTS)
	rm -f main mainopt
	rm -f ./*.vo ./*.vos ./*.vok

cleanml :
	rm -f $(MLFFILES) $(MLIFILES)

$(TESTS): axioms.cmx $(MLFFILES)
	@ocamlc -c $@.mli 
	@malfunction cmx -O2 $@.mlf

axioms.cmx: axioms.ml
	@ocamlopt -c axioms.ml

mainopt: $(MLFFILES) $(CMXFILES)
	@ocamlopt -c -w -a-1  main.ml 
	@ocamlopt -o mainopt unix.cmxa axioms.cmx $(CMXFILES) main.cmx

tests: tests.v
	@coqc $(COQOPTS) tests.v > /dev/null

build: $(TESTS) mainopt 

run: build
#	./main 10
	@echo "Malfunction with -O2 optimisations"
	./mainopt 10

.NOTPARALLEL: tests run