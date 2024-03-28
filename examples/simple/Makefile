all: Makefile.coq
	mkdir -p -m 0755 _build
	make -f Makefile.coq

_CoqProject: 
	git ls-files > _CoqProject

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

.PHONY: _CoqProject
