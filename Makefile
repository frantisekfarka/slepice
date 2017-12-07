RM=rm -f
TEX=pdflatex -interaction=nonstopmode
BIBTEX=bibtex
BIB=references.bib
COQDOC=coqdoc -g
COQC=coqc

TEX_DIR=tex/
SRC_DIR=src/
COQ_DIR=coq/
DOC_DIR=doc/
MAIN=exquan-raw.tex
#MAIN=exquan-nl-only.tex

META=$(SRC_DIR)fodtt-metavar.ott\
#     $(SRC_DIR)fodttstar-metavar.ott

FODTT= $(SRC_DIR)fodtt-flas_both.ott\
#$(SRC_DIR)fodtt-syntax.ott\
#      $(SRC_DIR)fodtt-typing.ott

#FODTTSTAR=$(SRC_DIR)fodttstar-syntax.ott

#FOHC=${SRC_DIR}fohc-metavar.ott\
#     ${SRC_DIR}fohc-syntax.ott
    
TRANS=#$(SRC_DIR)trans.ott


FODTTSTARLNL=$(SRC_DIR)fodttstar_lnl-syntax.ott\
	     $(SRC_DIR)fodtt_struct-syntax.ott\
	     $(SRC_DIR)fodtt_lnl-typing-algo.ott

FODTTLNL=#$(SRC_DIR)fodtt_lnl-syntax.ott\
	 #$(SRC_DIR)fodtt_lnl-typing.ott

#TRANSLNL=#$(SRC_DIR)trans-lnl.ott

TERMINALS=$(SRC_DIR)terminals.ott

#GOALS=$(SRC_DIR)fodtt_lnl-goal.ott



OTT=../ott/bin/ott

COQ=$(COQ_DIR)defns.v\
    $(COQ_DIR)nl_fusion.v\
    $(COQ_DIR)nl_sgn.v\
    $(COQ_DIR)nl_whr.v\
    $(COQ_DIR)nl_eq.v\
    $(COQ_DIR)nl_stralgeq.v\
    $(COQ_DIR)nl_walgeq.v\
    $(COQ_DIR)nl_struct.v\
    $(COQ_DIR)nl_tycheck.v

.PHONY: clean veryclean

default: $(MAIN)

watch:	$(MAIN)
	latexmk -pdf -pvc $(MAIN)

pdf: $(MAIN)
	latexmk -pdf $(MAIN)

exquan-raw.tex: $(META) \
	    $(FODTTSTAR) \
	    $(FODTT) \
	    $(FODTTSTARLNL) \
	    $(FOHC)\
	    $(TRANS) \
	    $(TRANSLNL) \
	    $(GOALS) \
	    $(TERMINALS)
	$(OTT) \
	    -o $@ \
	    -o $(COQ_DIR)defns.v \
	    -tex_wrap true\
	    -tex_name_prefix fodtt \
	    $(META) \
	    $(FODTTSTAR) \
	    $(FODTT) \
	    $(FODTTSTARLNL) \
	    $(FOHC)\
	    $(TRANS) \
	    $(TRANSLNL) \
	    $(GOALS) \
	    $(TERMINALS)

exquan-nl-only.tex: $(META) $(FODTTSTARLNL) $(FODTTLNL) $(SRC_DIR)fodtt_lnl-flas.ott 
	$(OTT) \
	    -tex_wrap true\
	    -tex_name_prefix fodtt \
	    -o $@ \
	    -o $(COQ_DIR)defns.v \
	    $(META) \
	    $(SRC_DIR)fodtt_lnl-flas.ott \
	    $(FODTTSTARLNL) \
	    $(TERMINALS) 

exquan-nl.tex: $(META) $(FODTT) $(FODTTSTAR) $(FODTTLNL) $(FODTTSTARLNL) $(TRANSLNL) $(TERMINALS) $(FOHC) $(GOALS)
	$(OTT) \
	    -tex_wrap true\
	    -tex_name_prefix fodtt \
	    -o $@ \
	    -o $(COQ_DIR)defns.v \
	    $(META) \
	    $(FODTTSTAR) \
	    $(FODTT) \
	    $(FODTTSTARLNL) \
	    $(FODTTLNL) \
	    $(TRANSLNL) \
	    $(FOHC) \
	    $(GOALS) \
	    $(TERMINALS) 


doc: $(COQ)
	$(COQDOC) --no-glob $(COQ) -d $(DOC_DIR)

coqc: $(COQ)
	$(COQC) $(COQ) 

#cleaning rules

clean:
	$(RM) *.aux *.xml *.bcf *.bbl *.blg *-blx.bib \
		*.log *.nav *.out *.vrb *.snm *.toc \
		X.tex *.bak *.pag *.fdb_latexmk *.fls \
		exquan-raw.tex exquan-nl.tex

veryclean: clean
	$(RM) *.pdf *.dvi

