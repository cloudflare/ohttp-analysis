### Tamarin Model of Oblivious HTTP

This repository contains a Tamarin model of [Oblivious HTTP](https://www.ietf.org/archive/id/draft-thomson-http-oblivious-01.html).



The main model is found in `ohttp.m4`, and can be built with: 

```bash
make
```



The model can be explored in Tamarin's interactive prover by running:

```bash
tamarin-prover interactive .
```



Proofs are stored in the `proofs` folder, and can be rechecked with:

```bash
make proofs
```



or alternatively explored in the interactive prover by running

```bash
tamarin-prover interactive proofs/
```


You can verify the proofs non-interactively by running:

```bash
$ tamarin-prover --prove proofs/OHTTP.spthy
[...]
==============================================================================
summary of summaries:

analyzed: OHTTP.spthy

MsgSources (all-traces): verified (53 steps)
end_to_end (exists-trace): verified (66 steps)
ss_match (all-traces): verified (9 steps)
secret_request (all-traces): verified (37 steps)
secret_response (all-traces): verified (50 steps)
secret_cid (all-traces): verified (6 steps)
request_binding (all-traces): verified (2 steps)
consistency (all-traces): verified (72 steps)
reach_nonce_reuse (all-traces): verified (85 steps)

==============================================================================
```


The proofs were generated using the develop version of Tamarin:

```
tamarin-prover 1.7.0, (C) David Basin, Cas Cremers, Jannik Dreier, Simon Meier, Ralf Sasse, Benedikt Schmidt, ETH Zurich 2010-2020
Git revision: 51ab611883cc99f07967d46fe6fb5b2686dbdf24, branch: develop
```



