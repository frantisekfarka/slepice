SLEPICE=../slepice

TESTS ?= no_T

.PHONY: $(TESTS) clean

default: $(TESTS)

%:
	$(SLEPICE) -sig $?.sig -term $?.tt -o $? > $?.out || true
	diff $?.out $?.exp_out

clean:
	$(RM) *.out
