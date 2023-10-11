COQOPTS = -R ../lib MetaCoq.VerifiedExtraction.Benchmarks.lib
CCOMPILER=gcc

# Names of the benchmarks
TESTS=$(shell cat TESTS)
# Names of the generated cfiles
MLFFILES=$(patsubst %,%.mlf, $(TESTS))
MLIFILES=$(patsubst %,%.mli, $(TESTS))
CMXFILES=$(patsubst %,%.cmx, $(TESTS))

default: tests run
all: tests main mainopt

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

$(TESTS): $(MLFFILES)
	if [ -a $@.mli ]; then ocamlc -c $@.mli ; fi;
	malfunction cmx $@.mlf

mainopt: $(MLFFILES) $(CMXFILES)
	ocamlopt -c main.ml
	ocamlopt -o mainopt unix.cmxa $(CMXFILES) main.cmx

tests: tests.v
	coqc $(COQOPTS) tests.v

run: $(TESTS) mainopt 
#	./main 10
	./mainopt 10