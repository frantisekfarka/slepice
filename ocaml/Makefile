OTT=~/STANDREWS/ott/bin/ott

OTT_SRC=../src/tt-meta.ott\
	../src/ttstar-syntax.ott\
	../src/tt-syntax.ott

OCAML_DOC=doc

.PHONY: ocaml clean
tt: ${OTT_SRC}
	${OTT} -o Parser.mly -o Lexer.mll -o ttstar.ml ${OTT_SRC}
	ed Lexer.mll < Lexer.ed
	ed Parser_pp.ml < Parser_pp.ed


build: tt
	ocamlbuild -use-menhir main.native

clean:
	ocamlbuild -clean
	rm -f Lexer.ml Parser.ml ttstar.ml Parser_pp.ml \
	   *mly *mll *mli *automaton *conflicts

veryclean: clean
	rm main.native
