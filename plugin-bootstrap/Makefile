
all: Makefile.coq
	make -f Makefile.coq

install: Makefile.coq all
	make -f Makefile.coq install

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

clean: Makefile.coq
	make -f Makefile.coq clean