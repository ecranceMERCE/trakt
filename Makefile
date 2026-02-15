all: Makefile.coq
	make all -f Makefile.coq

install: Makefile.coq
	make install -f Makefile.coq

clean: Makefile.coq.test
	make clean -f Makefile.coq.test

Makefile.coq : _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

Makefile.coq.test : _CoqProject.test
	coq_makefile -f _CoqProject.test -o Makefile.coq.test

all.test: Makefile.coq.test
	make all -f Makefile.coq.test

install.test: Makefile.coq.test all.test
	make install -f Makefile.coq.test
