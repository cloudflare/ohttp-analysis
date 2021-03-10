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



The proofs were generated using the develop version of Tamarin:

```
tamarin-prover 1.7.0, (C) David Basin, Cas Cremers, Jannik Dreier, Simon Meier, Ralf Sasse, Benedikt Schmidt, ETH Zurich 2010-2020
Git revision: 51ab611883cc99f07967d46fe6fb5b2686dbdf24, branch: develop
```



