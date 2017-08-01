RM=rm -f
TEX=pdflatex -interaction=nonstopmode
BIBTEX=bibtex
BIB=references.bib

TEX_DIR=tex/
SRC_DIR=src/
COQ_DIR=coq/
MAIN=exquan-raw.tex

META=$(SRC_DIR)fodtt-metavar.ott\
     $(SRC_DIR)fodttstar-metavar.ott

FODTT=$(SRC_DIR)fodtt-syntax.ott\
      $(SRC_DIR)fodtt-flas_both.ott\
      $(SRC_DIR)fodtt-typing.ott

FODTTSTAR=$(SRC_DIR)fodttstar-syntax.ott

FOHC=${SRC_DIR}fohc-syntax.ott\
    
TRANS=$(SRC_DIR)trans.ott

TERMINALS=$(SRC_DIR)terminals.ott

OTT=../ott/bin/ott

.PHONY: clean veryclean

default: $(MAIN)

watch:	$(MAIN)
	latexmk -pdf -pvc $(MAIN)

pdf: $(MAIN)
	latexmk -pdf $(MAIN)

exquan-raw.tex: $(META) $(FODTTSTAR) $(FODTT) $(FOHC) $(TRANS) $(TERMINALS)
	$(OTT) \
	    -o $@ \
	    -o $(COQ_DIR)defns.v \
	    $(META) \
	    $(FODTTSTAR) \
	    $(FODTT) \
	    $(FOHC) \
	    $(TRANS) \
	    $(TERMINALS)


#cleaning rules

clean:
	$(RM) *.aux *.xml *.bcf *.bbl *.blg *-blx.bib \
		*.log *.nav *.out *.vrb *.snm *.toc \
		X.tex *.bak *.pag *.fdb_latexmk *.fls \
		exquan-raw.tex

veryclean: clean
	$(RM) *.pdf *.dvi

