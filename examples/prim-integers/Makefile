
test: all
	./run

all:
	coqc append.v
	cp ../../lib/axioms-nocoq.ml axioms.ml
	cp -R ../../lib/coq-core .
	cd coq-core && ocamlopt -c int.mli int.ml uint63.mli uint63.ml
	ocamlopt -I coq-core -c axioms.ml
	ocamlopt -c append.mli
	malfunction cmx append.mlf
	ocamlopt -c main.ml
	ocamlopt coq-core/int.cmx coq-core/uint63.cmx axioms.cmx append.cmx main.cmx -o run
