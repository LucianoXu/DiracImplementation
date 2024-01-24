.SUFFIXES: .cmo .cmi .cmx .ml .mli

INCLUDE= 
CAMLC=ocamlc $(INCLUDE) 
CAMLLIBR=ocamlc $(INCLUDE) -a
CAMLCOPT=ocamlopt $(INCLUDE) 
CAMLLIBROPT=ocamlopt $(INCLUDE) -a

CAMLYACC=ocamlyacc
CAMLLEX=ocamllex

MODULES1=primitive_generator.cmo 
MODULES_OPT1= primitive_generator.cmx

byte:	primitive_generator prime_number


primitive_generator: $(MODULES1) primitive_generator.cmo
	$(CAMLC)  -o primitive_generator $(INCLUDE) $(MODULES1)


opt:	primitive_generator.opt prime_number.opt

prime_number: prim_number.cmo
	$(CAMLC) -o prime_number prim_number.cmo

prime_number.opt: prim_number.cmx
	$(CAMLCOPT) -o prime_number.opt prim_number.cmx


primitive_generator.opt: $(MODULES_OPT1)
	$(CAMLCOPT)  -o primitive_generator.opt $(MODULES_OPT1)
	strip primitive_generator.opt

all:	byte opt

.mli.cmi:
	$(CAMLC) -c $<

.ml.cmo:
	$(CAMLC) -c $<

.ml.cmx:
	$(CAMLCOPT) -c $<

clean:
	rm -f *.cmo
	rm -f *.cmi
	rm -f *.cmx
	rm -f *.o
	rm -f primitive_generator primitive_generator.opt
	rm -f *~
