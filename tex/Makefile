TEX=pdflatex -interaction=nonstopmode
BIBTEX=bibtex
BIB=references.bib

MAIN=slepice.tex
WRAPPER=wrapper.tex

.PHONY: clean veryclean

default: pdf 

watch:	$(MAIN) $(WRAPPER)
	latexmk -pdf -pvc $(WRAPPER) --jobname=$(MAIN:.tex=)

pdf: $(MAIN) $(WRAPPER)
	latexmk -pdf $(WRAPPER) --jobname=$(MAIN:.tex=)

#cleaning rules

clean:
	$(RM) *.aux *.xml *.bcf *.bbl *.blg *-blx.bib \
		*.log *.nav *.out *.vrb *.snm *.toc \
		X.tex *.bak *.pag *.fdb_latexmk *.fls \

veryclean: clean
	$(RM) *.pdf *.dvi 
