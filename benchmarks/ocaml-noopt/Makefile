COQOPTS =  -R ../lib MetaCoq.VerifiedExtraction.Benchmarks.lib -w -extraction-opaque-accessed,-notation-overridden,-opaque-let
CCOMPILER=gcc

# Names of the benchmarks
TESTS=$(shell cat TESTS)

default: tests run
all: tests run

.PHONY: run clean cleanml

mainopt:
	@ocamlbuild -use-ocamlfind -pkg core,core_bench,core_unix.command_unix -tag thread main.native

tests: tests.v
	@coqc $(COQOPTS) tests.v

run: mainopt
	@echo "OCaml with extraction optimisations off. Native:"
	@./main.native +time
