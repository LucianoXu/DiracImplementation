# MAKEFILE engendre par creemake

.SUFFIXES: .cmo .cmi .cmx .ml .mli

CAMLC=ocamlc -w A
CAMLLIBR=ocamlc -a
CAMLCOPT=ocamlopt 
CAMLLIBROPT=ocamlopt -a

CAMLYACC=ocamlyacc
CAMLLEX=ocamllex
MODULES=many_rules.cmo 

MODULES_OPT=many_rules.cmx 

many_rules: $(MODULES) many_rules.cmo
	# pour caml version unix
	$(CAMLC) -g -o many_rules $(MODULES) -cclib ""

many_rules.opt: $(MODULES_OPT) many_rules.cmx
	# pour camlopt version unix
	$(CAMLCOPT)  -o many_rules.opt $(MODULES_OPT)

.mli.cmi:
	$(CAMLC) -g -c $<

.ml.cmo:
	$(CAMLC) -g -c $<

.ml.cmx:
	$(CAMLCOPT) -c $<

clean:
	rm -f *.cmi
	rm -f *.cmo
	rm -f many_rules
	rm -f *.cmx
	rm -f *.o
	rm -f many_rules.opt




# graphe de dependances
many_rules.cmo: many_rules.ml
