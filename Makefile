RM=rm -f
TEX=pdflatex -interaction=nonstopmode
BIBTEX=bibtex
BIB=references.bib

TEX_DIR=tex/
SRC_DIR=src/
MAIN=exquan-raw.tex

FODTT=$(SRC_DIR)fodtt-metavar.ott\
      $(SRC_DIR)fodtt-syntax.ott\
      $(SRC_DIR)fodtt-flas_both.ott\
      $(SRC_DIR)fodtt-terminals.ott\
      $(SRC_DIR)fodtt-typing.ott

FODTTSTAR=$(SRC_DIR)fodttstar-metavar.ott\
	  $(SRC_DIR)fodttstar-syntax.ott

OTT=../ott/bin/ott

.PHONY: clean veryclean

default: $(MAIN)

watch:	$(MAIN)
	latexmk -pdf -pvc $(MAIN)

pdf: $(MAIN)
	latexmk -pdf $(MAIN)

exquan-raw.tex: $(FODTTSTAR) $(FODTT)
	$(OTT) \
	    -o $@ \
	    $(FODTTSTAR) \
	    $(FODTT) 


#cleaning rules

clean:
	$(RM) *.aux *.xml *.bcf *.bbl *.blg *-blx.bib \
		*.log *.nav *.out *.vrb *.snm *.toc \
		X.tex *.bak *.pag *.fdb_latexmk *.fls \
		exquan-raw.tex

veryclean: clean
	$(RM) *.pdf *.dvi

