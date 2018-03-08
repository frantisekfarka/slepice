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
	
.PHONY: clean 

default: build

$(TO_PATCH): $(addsuffix .patched,$(TO_PATCH))

%.patched: %.ed
	ed -v $* < $< 
	touch $@

$(COQ_FILES): $(addprefix, $(COQ_DIR),COQ_FILES)
	cp $(COQ_DIR)$@ .


build: $(TO_PATCH) $(COQ_FILES)
	ocamlbuild -use-menhir main.native

#cleaning rules

clean:
	ocamlbuild -clean
	$(RM) $(COQ_FILES) $(TO_PATCH) *.patched


veryclean: clean
	$(RM) main.native
