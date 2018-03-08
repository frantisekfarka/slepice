OTT=ott
ML_DIR=../ocaml/
COQ_DIR=../coq/
TEX_DIR=../tex/
SRC_DIR=./

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


OTT_SRC= $(META)\
	$(FODTTSTAR)\
	$(FODTT)\
	$(FOHC)\
	$(TRANS)\
	$(REFIN)\
	$(TERMINALS)\
	$(FORMULAE)

OTT_OUT=Parser.mly\
	Lexer.mll\
	Defns.ml\
	$(COQ_DIR)Defns.v\
	$(TEX_DIR)slepice.tex

.PHONY: clean

default: $(OTT_OUT)
	cp Defns.ml $(ML_DIR)
	cp Lexer.mll $(ML_DIR)
	cp Parser.mly $(ML_DIR)
	cp Parser_pp.ml $(ML_DIR)

$(OTT_OUT): $(OTT_SRC)
	$(OTT) -tex_wrap false -tex_name_prefix tt \
	    $(addprefix -o ,$(OTT_OUT)) $(OTT_SRC)

clean:
	$(RM) $(OTT_OUT) $(ML_DIR)Defns.ml
