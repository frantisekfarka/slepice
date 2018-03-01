OTT=~/STANDREWS/ott/bin/ott

OTT_SRC=../src/ttstar-syntax.ott

.PHONY: ocaml clean
ocaml: ${OTT_SRC}
	${OTT} -i ${OTT_SRC} -o Parser.mly -o Lexer.mll -o LF.ml
	#patch Lexer.mll Lexer.diff
	#ed Parser_pp.ml < Parser_pp.diff

build:
	ocamlbuild -tag thread -use-menhir -use-ocamlfind -pkg core main.native


clean:
	rm -f Lexer.ml Parser.ml LF.ml Parser_pp.ml \
	   *mly *mll *mli *automaton *conflicts

