DIRS= .
INCLUDES=$(patsubst %,-I %, $(DIRS))

FINAL := Main

LIB := 	Utils Lattices LibTactics

TMU := 	Semantics Instr

TMU_A:= AbstractCommon AbstractMachine	\
	Rules QuasiAbstractMachine

TMU_AMNI := NIAbstractMachine

TMU_ANI := TINI Refinement TINI_inf

TMU_C := CLattices Concrete ConcreteMachine \
	CodeGen CodeTriples CodeSpecs FaultRoutine\
	Determinism RefinementAC ConcreteExecutions \
	NIConcreteMachine RefinementCA Encodable CLabels

ALLV := $(LIB) $(FINAL) $(TMU) $(TMU_A) $(TMU_AMNI) $(TMU_ANI) $(TMU_C) 

VS := $(ALLV:%=%.v) 

COQEXEC=coqtop $(INCLUDES) -batch -load-vernac-source

DEP2DOT=../dep2dot/dep2dot

.PHONY: coq doc clean

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

all: coq

Makefile.coq: Makefile $(VS:%=%)
	echo $(VS)
	coq_makefile $(INCLUDES) $(VS) -o Makefile.coq

coq.timestamp: Makefile.coq
	date > coq.timestamp
	$(MAKE) -f Makefile.coq || rm coq.timestamp

clean:
	rm -f Makefile.coq .depend *.v.d *.vo *.glob *~
	rm -fr html
	rm -f $(patsubst %, %/*.vo, $(DIRS))
	rm -f $(patsubst %, %/*.v.d, $(DIRS))
	rm -f $(patsubst %, %/*.glob, $(DIRS))
	rm -f $(patsubst %, %/*~, $(DIRS))
	rm -f $(patsubst %, %/*.o, $(DIRS))

doc:
	$(MAKE) -f Makefile.coq html

view-deps:
	coqdep -I . *.v | $(DEP2DOT) | dot -Txlib &
