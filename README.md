# Accountability for the sElect voting protocol

This repository contains EasyCrypt code for defining accountability for 
electronic voting protocols and a proof that the sElect voting protocol
satisfies accountability.

To check the proof, either 
	-	install EasyCrypt’s `r2022.04` release (following instructions at https://github.com/easycrypt/easycrypt) and pinning to the release tag. You can then run `make check` to confirm that all proofs validate, or
	-	run `docker run -v$PWD:/home/charlie/sacc docker.io/easycryptpa/ec-test-box:r2022.04 sh -c "cd sacc; opam exec -- make check”`

The proof is known to check with the release (r2022.04) version of EasyCrypt with the following SMT solvers installed:
  - Z3 version 4.8.10
  - CVC4 version 1.8
  - Alt-Ergo version 2.4.0

`AccountabilityDefinition.ec` models the security experiment for accountability.

`SelectDefinition.ec` models the sElect voting system.

`SelectAccountability.ec` proves that sElect satisfies this notion of security. 
