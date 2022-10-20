Q     := @
SPTHY := ohttp.spthy

.PHONY: all proofs clean
all: $(SPTHY)

proofs: ; $Qtamarin-prover --prove proofs/*

clean:  ; $Qrm -f $(SPTHY)

%.spthy: %.m4 ; $Qm4 $< > $@
