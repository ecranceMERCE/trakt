all: Makefile.coq
	make all -f Makefile.coq

install: Makefile.coq
	make install -f Makefile.coq

clean: Makefile.coq
	make clean -f Makefile.coq

Makefile.coq : _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq
