SLEPICE=../slepice

TESTS ?= no_T idA

.PHONY: $(TESTS) clean

default: $(TESTS:=.test)

%.test: %.out %.prog %.g
	@echo "Test" $* "passed"

%.out %.prog %.g: %.sig %.tt
	$(SLEPICE) -sig $*.sig -term $*.tt -o $* > $*.out || true
	diff $*.exp_out $*.out

clean:
	$(RM) *.out
