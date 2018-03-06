OTT=~/STANDREWS/ott/bin/ott

OTT_SRC= ../src/ttstar-meta.ott\
	../src/tt-meta.ott\
	../src/ttstar-syntax.ott\
	../src/tt-syntax.ott\
	../src/fohc-meta.ott\
	../src/fohc-syntax.ott

COQ_DIR=../coq/
COQ_FILES=$(COQ_DIR)Eq.ml\
	$(COQ_DIR)Sgn.ml\
	$(COQ_DIR)Refin.ml\
	$(COQ_DIR)Datatypes.ml\
	$(COQ_DIR)Specif.ml

COQ_GEN=coq/

ED_PATCH=Parser.ed\
	Lexer.ed\
	Parser_pp.ed\
	Defns.ed
	
OTT_ML=Parser.mly\
       Lexer.mll\
       Defns.ml

.PHONY: ocaml clean coq

$(OTT_ML): ${OTT_SRC} ${ED_PATCH}
	${OTT} -o Parser.mly -o Lexer.mll -o Defns.ml ${OTT_SRC}
	ed Lexer.mll < Lexer.ed
	ed Parser_pp.ml < Parser_pp.ed
	ed Parser.mly < Parser.ed
	ed Defns.ml < Defns.ed

tt: $(OTT_ML)

coq: 
	#todo ott dir
	make -C ../ 
	make -C $(COQ_DIR) all
	mkdir -p $(COQ_GEN)
	cp $(COQ_FILES) $(COQ_GEN)


build: $(OTT_ML) coq
	ocamlbuild -I $(COQ_GEN) -use-menhir main.native

clean:
	ocamlbuild -clean
	rm -f Lexer.ml Parser.ml ttstar.ml Parser_pp.ml \
	   *mly *mll *mli *automaton *conflicts
	rm -f $(COQ_GEN)*ml
	rmdir $(COQ_GEN)

veryclean: clean
	rm main.native
