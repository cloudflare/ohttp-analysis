Q     := @
SPTHY := ohttp.spthy

.PHONY: all proofs clean
all: $(SPTHY)

proofs: ; $Qtamarin-prover proofs/*

clean:  ; $Qrm -f $(SPTHY)

%.spthy: %.m4 ; $Qm4 $< > $@
