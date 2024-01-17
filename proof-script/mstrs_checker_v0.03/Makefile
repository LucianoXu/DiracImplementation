MAIN=mstrsck
SML=sml
MLYACC=ml-yacc
MLLEX=ml-lex
MLTON=mlton
MLTONLEX=mllex
MLTONYACC=mlyacc
RESULTS=o

all: $(MAIN).x86-linux

.yacc.sml:
	$(MLYACC) $<

.lex.sml:
	$(MLLEX) $<

%.x86-linux: sources.cm mstrs.lex.sml mstrs.yacc.sml fotrs.lex.sml fotrs.yacc.sml *.sml
	ml-build $< Main.main $@

mstrs.lex.sml: mstrs.yacc.sml mstrs.lex
	ml-lex mstrs.lex

mstrs.yacc.sml: mstrs.yacc
	ml-yacc $<

fotrs.lex.sml: fotrs.yacc.sml fotrs.lex
	ml-lex fotrs.lex

fotrs.yacc.sml: fotrs.yacc
	ml-yacc $<

native: mstrsck.mlb *.sml
	$(MLTONYACC) mstrs.yacc
	$(MLTONLEX) mstrs.lex
	$(MLTONYACC) fotrs.yacc
	$(MLTONLEX) fotrs.lex
	$(MLTON) -link-opt '-static' mstrsck.mlb

clean:
	$(RM) *.x86-linux *~ mstrs.yacc.sml mstrs.lex.sml mstrs.yacc.sig fotrs.yacc.sml fotrs.lex.sml fotrs.yacc.sig mstrsck

.PHONY : all clean
