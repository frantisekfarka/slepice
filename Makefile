RM=rm -f
TEX=pdflatex -interaction=nonstopmode
BIBTEX=bibtex
BIB=references.bib

TEX_DIR=tex/
VERB_DIR=verb/
MAIN=exquan.tex



OTT=../ott/bin/ott

.PHONY: clean veryclean

default: $(MAIN)
	latexmk -pdf $(MAIN)

watch:	$(MAIN)
	latexmk -pdf -pvc $(MAIN)

exquan.tex: exquan.ott
	$(OTT) -i exquan.ott -o exquan.tex

#cleaning rules

clean:
	$(RM) *.aux *.xml *.bcf *.bbl *.blg *-blx.bib \
		*.log *.nav *.out *.vrb *.snm *.toc \
		X.tex *.bak *.pag 

veryclean: clean
	$(RM) *.pdf *.dvi

