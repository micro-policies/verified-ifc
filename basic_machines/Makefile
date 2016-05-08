all: Makefile.coq
	make -f Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

.PHONY: clean

clean: Makefile.coq
	make clean -f Makefile.coq
	rm -rf Makefile.coq
