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
	
.PHONY: ocaml clean coqfiles foo

default: build

$(TO_PATCH): $(addsuffix .patched,$(TO_PATCH))

%.patched: %.ed
	ed $* < $< 
	touch $@

coqfiles: $(COQ_FILES) 
	cp $(COQ_FILES) .


build: $(TO_PATCH) coqfiles
	ocamlbuild -use-menhir main.native

#cleaning rules

clean:
	ocamlbuild -clean
	$(RM) $(COQ_FILES) $(TO_PATCH) *.patched


veryclean: clean
	$(RM) main.native
