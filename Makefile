DATE=`date --i`

all: basic_machines/Makefile extended_machines/Makefile
	make -j -C basic_machines
	make -j -C extended_machines

basic_machines/Makefile: basic_machines/_CoqProject
	cd basic_machines; coq_makefile -f _CoqProject -o Makefile

extended_machines/Makefile: extended_machines/_CoqProject
	cd extended_machines; coq_makefile -f _CoqProject -o Makefile

clean:
	make clean -C basic_machines
	make clean -C extended_machines

distrib: all
	cd ../..; git archive --format=zip --prefix=verified-ifc-coq/ HEAD:verif/pico-ifc-coq/ > verif/pico-ifc-coq/verified-ifc-coq-${DATE}.zip
