
DATE=`date --i`

all:
	make -j -C basic_machines
	make -j -C extended_machines

clean:
	make clean -C basic_machines
	make clean -C extended_machines

distrib: all
	cd ../..; git archive --format=zip --prefix=verified-ifc-coq/ HEAD:verif/pico-ifc-coq/ > verif/pico-ifc-coq/verified-ifc-coq-${DATE}.zip
