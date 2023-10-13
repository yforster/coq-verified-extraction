COQOPTS = -R ../lib MetaCoq.VerifiedExtraction.Benchmarks.lib
CCOMPILER=gcc

# Names of the benchmarks
TESTS=$(shell cat TESTS)
# Names of the generated cfiles
MLFFILES=$(patsubst %,%.mlf, $(TESTS))
MLIFILES=$(patsubst %,%.mli, $(TESTS))
CMXFILES=$(patsubst %,%.cmx, $(TESTS))

default: tests run
all: tests mainopt

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
	ocamlc -c $@.mli 
	malfunction cmx $@.mlf

axioms.cmx: axioms.ml
	ocamlopt -c axioms.ml

mainopt: $(MLFFILES) $(CMXFILES)
	ocamlopt -c main.ml 
	ocamlopt -o mainopt unix.cmxa axioms.cmx $(CMXFILES) main.cmx

tests: tests.v
	coqc $(COQOPTS) tests.v

build: $(TESTS) mainopt 

run: build
#	./main 10
	./mainopt 10
