# Formalizing the KZG-Polynomial-Commitment-Scheme in Isabelle/HOL

## Isabelle/HOL
[Isabelle/HOL](https://isabelle.in.tum.de/) is an open-source interactive theorem prover. The version used for this formalization is Isabelle2022 (as of writing this the most recent version).

## Reference Paper
This formalization follows the original [paper](https://cacr.uwaterloo.ca/techreports/2010/cacr2010-10.pdf):  
A. Kate, G. Zaverucha, and I. Goldberg. Polynomial commitments. Technical report, 2010. CACR 2010-10, Centre for Applied Cryptographic Research, University
of Waterloo
First step is to prove the DL version.


## Correctness
Correctness i.e. the interaction between an honest prover and an honest verifier, yields a correct result.
#### Proven.

## Security Properties
The security properties are the same as in the [paper](https://cacr.uwaterloo.ca/techreports/2010/cacr2010-10.pdf).
They are shown via game-based proofs, see the [CryptHOL tutorial](https://eprint.iacr.org/2018/941.pdf) for details.

### Polynomial Binding
In the reduction to the t-strong Diffie Hellmann game, the factorization of polynomials over finite fields is needed, which is not completely supported in Isabelle as of now (only for square-free polynomials). The current task, therefore, is to formalize the factorization. Other than factorization, the property is proven.
#### Almost proven.

### Evaluation Binding
#### Open.

### Hiding
#### Open.


