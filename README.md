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
(thanks to [Katharina Kreuzer](https://www21.in.tum.de/team/kreuzer/) for providing the Elimination of repeated factors (ERF) algorithm, which allowed a complete factorization)

#### Proven.

### Evaluation Binding
#### Proven.

### Hiding
#### In Progress..

### Knowledge Soundness in the Algebraic Group Model (AGM)
Though this property is not explicitly stated in the original paper, it is commonly referred to and needed for zk-SNARK protocols, such as PLONK and Sonic.
#### Proven.

## Batch version

### Correctness

#### Proven.

### Binding

#### Proven.

### Hiding 

#### Open. 

### Knowledge Soundness

#### Proven.


