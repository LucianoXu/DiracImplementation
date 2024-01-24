# MAKEFILE engendre par creemake

.SUFFIXES: .cmo .cmi .cmx .ml .mli

CAMLC=ocamlc -w A
CAMLLIBR=ocamlc -a
CAMLCOPT=ocamlopt 
CAMLLIBROPT=ocamlopt -a

CAMLYACC=ocamlyacc
CAMLLEX=ocamllex
MODULES=gen_sn.cmo 

MODULES_OPT=gen_sn.cmx 

opt: gen_sn_complete.opt

gen_sn_complete: gen_sn_complete.cmo
	$(CAMLC) -g -o gen_sn_complete gen_sn_complete.cmo

gen_sn_complete.opt: gen_sn_complete.cmx
	$(CAMLCOPT) -o gen_sn_complete.opt gen_sn_complete.cmx

gen_sn: $(MODULES) gen_sn.cmo
	$(CAMLC) -g -o gen_sn $(MODULES) -cclib ""

gen_sn.opt: $(MODULES_OPT) gen_sn.cmx
	$(CAMLCOPT)  -o gen_sn.opt $(MODULES_OPT)

.mli.cmi:
	$(CAMLC) -g -c $<

.ml.cmo:
	$(CAMLC) -g -c $<

.ml.cmx:
	$(CAMLCOPT) -c $<

clean:
	rm -f *.cmi
	rm -f *.cmo
	rm -f gen_sn
	rm -f *.cmx
	rm -f *.o
	rm -f gen_sn.opt
	rm -f gen_sn_complete.opt
	rm -f gen_sn_complete

# graphe de dependances
gen_sn.cmo: gen_sn.ml
