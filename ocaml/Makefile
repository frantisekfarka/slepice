COQ_DIR=../coq/
COQ_FILES=Eq.ml\
	Sgn.ml\
	Refin.ml\
	Datatypes.ml\
	Specif.ml

TO_PATCH=Parser.mly\
	Lexer.mll\
	Parser_pp.ml\
	Defns.ml

PATCHED=$(addsuffix .patched,$(TO_PATCH))

.PHONY: clean default build

default: build

$(PATCHED):%.patched:% %.ed 
	ed -v $< < $<.ed && touch $@

$(COQ_FILES): $(addprefix, $(COQ_DIR),COQ_FILES)
	cp $(COQ_DIR)$@ .


build: $(PATCHED) $(COQ_FILES)
	ocamlbuild -use-ocamlfind -use-menhir main.native

#cleaning rules

clean:
	ocamlbuild -clean
	$(RM) $(COQ_FILES) $(TO_PATCH) *.patched


veryclean: clean
	$(RM) main.native
