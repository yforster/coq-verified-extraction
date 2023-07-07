all:
	cp ../../compile_malfunction.mlf compile_malfunction.mlf
	cp ../primitives/*.ml* .
	ocamlopt primInt63.mli primInt63.ml float64_common.mli float64_common.ml primFloat.mli primFloat.ml
	ocamlc -opaque -c compile_malfunction.mli
	malfunction fmt compile_malfunction.mlf > compile_malfunction_fmt.mlf
	yes | mv  compile_malfunction_fmt.mlf compile_malfunction.mlf
	../fix_primitives.sh compile_malfunction.mlf
	malfunction cmx compile_malfunction.mlf
	# ocamlopt test_add.cmx main.ml -o main
	# ./main
