RM=rm -f
TEX=pdflatex -interaction=nonstopmode
BIBTEX=bibtex
BIB=references.bib
OTT=../ott/bin/ott

TEX_DIR=tex/
SRC_DIR=src/
COQ_DIR=coq/
DOC_DIR=doc/
ML_DIR=ocaml/
MAIN=exquan.tex
WRAPPER=wrapper.tex

META=\
     $(SRC_DIR)ttstar-meta.ott\
     $(SRC_DIR)tt-meta.ott\

FORMULAE=\
     $(SRC_DIR)formulae.ott

FODTTSTAR=$(SRC_DIR)ttstar-syntax.ott\

FODTT=$(SRC_DIR)tt-syntax.ott\
#    $(SRC_DIR)tt-typing_algo.ott\
#     #$(SRC_DIR)tt-typing.ott\

FOHC=${SRC_DIR}fohc-meta.ott\
     ${SRC_DIR}fohc-syntax.ott
    
TRANS=#$(SRC_DIR)trans.ott

REFIN=$(SRC_DIR)refin.ott

TERMINALS=$(SRC_DIR)terminals.ott


.PHONY: clean veryclean

default: $(MAIN)

watch:	$(MAIN) $(WRAPPER)
	latexmk -pdf -pvc $(WRAPPER) --jobname=$(MAIN:.tex=)

pdf: $(MAIN) $(WRAPPER)
	latexmk -pdf $(WRAPPER) --jobname=$(MAIN:.tex=)

exquan.tex: $(META) \
	    $(FODTTSTAR) \
	    $(FODTT) \
	    $(FOHC)\
	    $(TRANS) \
	    $(REFIN) \
	    $(TERMINALS) \
    	    $(FORMULAE) 
	$(OTT) \
	    -o $@ \
	    -o $(COQ_DIR)Defns.v \
	    -tex_wrap false\
	    -tex_name_prefix fodtt \
	    $^

doc: coqdoc

coqdoc:
	make -C $(COQ_DIR) gallinahtml
	cp -r $(COQ_DIR)html/*.html $(COQ_DIR)html/*.css $(DOC_DIR)

coqc: $(COQ)
	$(COQC) $(COQ) 

#cleaning rules

clean:
	$(RM) $(DOC_DIR)/.*
	$(RM) *.aux *.xml *.bcf *.bbl *.blg *-blx.bib \
		*.log *.nav *.out *.vrb *.snm *.toc \
		X.tex *.bak *.pag *.fdb_latexmk *.fls \
		$(MAIN)
	make -C $(ML_DIR) clean

veryclean: clean
	$(RM) *.pdf *.dvi 

