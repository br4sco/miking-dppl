CPPL := ../../../../../build/cppl
EXAMPLES := \
	bayesian-parameter-estimation-run.json \
	bayesian-parameter-estimation-ivp-sensitivity-run.json \
	bayesian-parameter-estimation-ivp-solution-run.json \
	bayesian-parameter-estimation-ivp-solution-trace-run.json \
	bayesian-parameter-estimation-ivp-sensitivity-trace-run.json \
	ode-sensitivites-two-methods-run.json \
	ode-sensitivites-two-methods-scalar-run.json \
	rode-run.json \
	tumor-inhibitor-rode-run.json

.PHONY: all
all: $(EXAMPLES)

.PHONY: plots
plots:
	python plot.py

%.exe: %.mc
	$(CPPL) --seed 1 --dppl-typecheck --output $@ $<

%.json: %.exe
	./$<

.PHONY: clean
clean:
	rm -rf *.json *.exe
