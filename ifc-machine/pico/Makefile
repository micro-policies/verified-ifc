DIRS=lib common tmu tmu/amach tmu/cmach tmu/amach_ni tmu/abstract_ni .
INCLUDES=$(patsubst %,-I %, $(DIRS))

FINAL := Altogether

LIB := 	Utils Monad Lattices LatticeHL LibTactics

COMMON:= NotionsOfNI Simulation LNIwithEvents LockStepNI BwdSimNI

TMU := 	TMUInstr

TMU_A:=	Abstract Rules AbstractCommon QuasiAbstractMachine AbstractMachineFun

TMU_AMNI := AbstractObsEquiv AbstractObsEquivFun NIAbstractMachine

TMU_ANI := TINI

TMU_C := CLattices WfCLattices Concrete ConcreteMachineSmallStep \
	CodeGen CodeSpecs FaultRoutine\
	Refinement Determinism

VS := $(LIB:%=lib/%.v) $(COMMON:%=common/%.v) $(TMU:%=tmu/%.v) \
	$(TMU_A:%=tmu/amach/%.v) $(TMU_C:%=tmu/cmach/%.v) \
	$(TMU_AMNI:%=tmu/amach_ni/%.v) $(TMU_ANI:%=tmu/abstract_ni/%.v) \
	$(FINAL:%=%.v)

EXTRACTDIR := extraction/
EXTRACTION := $(EXTRACTDIR)Extraction.v
ALLDIRS := $(EXTRACTDIR) $(DIRS) driver

COQEXEC=coqtop $(INCLUDES) -batch -load-vernac-source

.PHONY: coq doc clean

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

all: coq extraction

Makefile.coq: Makefile $(VS:%=%)
	echo $(VS)
	coq_makefile $(INCLUDES) $(VS) -o Makefile.coq

coq.timestamp: Makefile.coq
	date > coq.timestamp
	$(MAKE) -f Makefile.coq || rm coq.timestamp

extraction: extraction.timestamp

extraction.timestamp: coq.timestamp $(EXTRACTION)
	date > extraction/extraction.timestamp
	$(COQEXEC) $(EXTRACTION)
	cd extraction && ./add_safe_prelude.sh && ghc --make Main
	rm -rf extraction.timestamp

clean:
	rm -f Makefile.coq .depend *.v.d *.vo *.glob *~
	rm -fr html
	rm -f $(patsubst %, %/*.vo, $(ALLDIRS))
	rm -f $(patsubst %, %/*.v.d, $(ALLDIRS))
	rm -f $(patsubst %, %/*.glob, $(ALLDIRS))
	rm -f $(patsubst %, %/*~, $(ALLDIRS))
	rm -f $(patsubst %, %/*.hi, $(ALLDIRS))
	rm -f $(patsubst %, %/*.ho, $(ALLDIRS))
	rm -f $(patsubst %, %/*.o, $(ALLDIRS))
	rm -f driver/Driver
	rm -f $(EXTRACTDIR)*.hs
	rm -f $(EXTRACTDIR)extraction.timestamp
	rm -f coq.timestamp

doc:
	$(MAKE) -f Makefile.coq html
