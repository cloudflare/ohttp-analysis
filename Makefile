%.spthy: %.m4
	m4 $< > $@

.PHONY: all
all: ohttp.spthy 

.PHONY: proofs
proofs:
	tamarin-prover proofs/*

.PHONY: clean
clean:
	rm ohttp.spthy
