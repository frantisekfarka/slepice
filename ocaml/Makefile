COQ_DIR=../coq/
COQ_FILES=$(COQ_DIR)Eq.ml\
	$(COQ_DIR)Sgn.ml\
	$(COQ_DIR)Refin.ml\
	$(COQ_DIR)Datatypes.ml\
	$(COQ_DIR)Specif.ml

TO_PATCH=Parser.mly\
	Lexer.mll\
	Parser_pp.ml\
	Defns.ml
	
.PHONY: ocaml clean coq foo

$(TO_PATCH): $(addsuffix .patched,$(TO_PATCH))
	cp $< $@ 

%.patched: %.ed
	ed $* < $< > $@

coqfiles: $(COQ_FILES) 
	cp $(COQ_FILES) .


build: $(TO_PATCH) coqfiles
	ocamlbuild -use-menhir main.native

#cleaning rules

clean:
	ocamlbuild -clean

veryclean: clean
	$(RM) main.native
