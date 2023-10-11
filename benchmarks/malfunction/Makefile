COQOPTS = -R ../lib MetaCoq.VerifiedExtraction.Benchmarks.lib
CCOMPILER=gcc

# Names of the benchmarks
TESTS=$(shell cat TESTS)
# Names of the generated cfiles
MLFFILES=$(patsubst %,%.mlf, $(TESTS))
MLIFILES=$(patsubst %,%.mli, $(TESTS))
CMOFILES=$(patsubst %,%.cmo, $(TESTS))
CMXFILES=$(patsubst %,%.cmx, $(TESTS))

default: tests run
all: tests main mainopt

.PHONY: run clean cleanml

$(MLFILES): tests
$(CMOFILES): $(TESTS)
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
#	ocamlc -c $@.mli
	malfunction cmx $@.mlf

main: $(CMOFILES) $(CMXFILES)
#	ocamlc -c main.ml
	ocamlopt -c main.ml
	# ocamlc -o main unix.cma $(CMOFILES) main.cmo 
#	ocamlopt -o mainopt unix.cmxa $(CMXFILES) main.cmx
	ocamlopt -o mainopt unix.cmxa demo1.cmx main.cmx

tests: tests.v
	coqc $(COQOPTS) tests.v

run: mainopt
#	./main 10
	./mainopt 10
