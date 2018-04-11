SLEPICE=../slepice

TESTS ?= no_T idA fromJust-full

.PHONY: $(TESTS) clean

default: $(TESTS:=.test)

%.test: %.out %.prog %.g
	@echo "Test" $* "passed"

%.out %.prog %.g: %.sig %.tt
	@$(SLEPICE) -sig $*.sig -term $*.tt -o $* > $*.out \
		&& diff $*.exp_prog $*.prog \
		&& diff $*.exp_g $*.g || true
	@diff $*.exp_out $*.out 

clean:
	$(RM) *.out *.prog *.g
