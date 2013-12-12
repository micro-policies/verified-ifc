DIRS=.
INCLUDES=$(patsubst %,-I %, $(DIRS))

COQC=coqc -q $(INCLUDES)
COQDEP=coqdep $(INCLUDES)
COQEXEC=coqtop $(INCLUDES) -batch -load-vernac-source
DEP2DOT=../dep2dot/dep2dot

VS=\
	Utils.v Lattices.v LibTactics.v \
	Semantics.v Instr.v \
	AbstractCommon.v AbstractMachine.v \
	Rules.v QuasiAbstractMachine.v \
	TINI.v NIAbstractMachine.v \
	Refinement.v TINI_inf.v \
	Concrete.v \
	CodeGen.v ConcreteMachine.v Determinism.v \
	ConcreteExecutions.v CodeTriples.v CodeSpecs.v \
	Encodable.v CLattices.v  CLabels.v \
	FaultRoutine.v RefinementAC.v \
	NIConcreteMachine.v \
	RefinementCA.v Main.v

proof: $(VS:.v=.vo)

.PHONY: coq doc clean proof

all: 
	make proof
	make documentation

documentation: doc/coq2html $(VS)
	mkdir -p doc/html
	rm -f doc/html/*.html
	doc/coq2html -o 'doc/html/%.html' doc/*.glob \
          $(filter-out doc/coq2html, $^)
	cp doc/coq2html.css doc/coq2html.js doc/html/

doc/coq2html: doc/coq2html.ml
	ocamlopt -o doc/coq2html str.cmxa doc/coq2html.ml

doc/coq2html.ml: doc/coq2html.mll
	ocamllex doc/coq2html.mll

latexdoc:
	cd doc; $(COQDOC) --latex -o doc/doc.tex -g $(VS)

.SUFFIXES: .v .vo

.v.vo:
	@rm -f doc/glob/$(*F).glob 
	@echo "COQC $*.v" 
	@$(COQC) -dump-glob doc/$(*F).glob $*.v

depend: 
	$(COQDEP) $(VS) > .depend

clean:
	rm -f Makefile.coq *.v.d *.vo *~
	rm -fr html
	rm -rf doc/html doc/*.glob doc/*~
	rm -f doc/coq2html.ml doc/coq2html
	rm -f doc/coq2html.{cmi,cmx,o}
	rm -f $(patsubst %, %/*.vo, $(DIRS))
	rm -f $(patsubst %, %/*.v.d, $(DIRS))
	rm -f $(patsubst %, %/*.glob, doc)
	rm -f $(patsubst %, %/*~, $(DIRS))
	rm -f $(patsubst %, %/*.o, $(DIRS))

view-deps:
	coqdep -I . *.v | $(DEP2DOT) | dot -Txlib &

include .depend
