DIRS= .
INCLUDES=$(patsubst %,-I %, $(DIRS))

LIB := 	Utils Lattices LibTactics

TMU := 	Semantics Instr Memory

TMU_A:= AbstractCommon AbstractMachine	\
	Rules QuasiAbstractMachine Refinement RefinementQAC RefinementAC RefinementAQA

TMU_AMNI := NIAbstractMachine

TMU_ANI := TINI Refinement

TEMP := CLattices Concrete ConcreteMachine CodeGen \
        Determinism ConcreteExecutions CodeSpecs \
	FaultRoutine NIConcreteMachine

ARR := CodeTriples

ALLV := $(LIB) $(TMU) $(TMU_A) $(TMU_AMNI) $(TMU_ANI) $(TEMP) $(ARR) #$(TMU_C)

VS := $(ALLV:%=%.v) 

COQEXEC=coqtop $(INCLUDES) -batch -load-vernac-source

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
