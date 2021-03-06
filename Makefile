TEX_DIR=tex/
SRC_DIR=src/
COQ_DIR=coq/
DOC_DIR=doc/
TEST_DIR=test/
ML_DIR=ocaml/

OTT_DIR ?= $(shell pwd)/ott

.PHONY: clean veryclean slepice coq ott

default: slepice 

slepice: ott coq ocaml
	cp $(ML_DIR)main.native slepice

ott:
	PATH=$(OTT_DIR)/bin:$(PATH) make -C $(SRC_DIR)

coq:
	make -C $(COQ_DIR)

ocaml: coq
	make -C $(ML_DIR)

doc: coqdoc texdoc

coqdoc:
	make -C $(COQ_DIR) gallinahtml
	cp -r $(COQ_DIR)html/*.html $(COQ_DIR)html/*.css $(DOC_DIR)

texdoc:
	make -C $(TEX_DIR)
	cp $(TEX_DIR)slepice.pdf $(DOC_DIR)

test: slepice
	make -C $(TEST_DIR)

#cleaning rules

clean:
	make -C $(TEX_DIR) clean
	make -C $(SRC_DIR) clean
	make -C $(ML_DIR) clean
	make -C $(COQ_DIR) clean
	make -C $(TEST_DIR) clean
	$(RM) $(COQ_DIR)*.ml $(COQ_DIR)*.mli

veryclean: clean
	make -C $(TEX_DIR) veryclean
	make -C $(OTT_DIR)/ott clean
	$(RM) slepice $(DOC_DIR)*

