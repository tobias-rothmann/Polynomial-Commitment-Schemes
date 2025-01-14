# Formalizing Polynomial Commitment Schemes in Isabelle/HOL


## Abstract 
We formalize the notion of polynomial commitment schemes (PCSs) in the interactive theorem prover Isabelle/HOL and formally verify two KZG versions' security proofs. 
We formalize an abstract definition of polynomial commitment schemes and abstract games for correctness, binding, hiding, and knowledge soundness/extractability, unifying the notion of security for PCSs. 
We formally verify the security proofs for two PCSs; the standard DL-version KZG and a batched version of the KZG. 
Our proofs follow the sequence-of-games approach proposed by Shoup, with machine-checked transitions, as is the standard in the CryptHOL framework for formal verification of cryptography in Isabelle.
To our knowledge, this is the first formalization of polynomial commitment schemes and the first formal verification of any concrete polynomial commitment scheme's security proofs. This is a work in progress; while the bulk of the work is already done (formalization of PCSs and according games, formal verification of the KZG and the batched KZG), there are still some remaining tasks and ongoing revisions we would like to implement; most notably we want to formalize the AGM properly.

## Isabelle/HOL
[Isabelle/HOL](https://isabelle.in.tum.de/) is an open-source interactive theorem prover. The version used for this formalization is Isabelle2024 (as of writing this the most recent version).

## Formalizing an abstract Polynomial Commitment Scheme

We formalize an abstract polynomial commitment scheme and corresponding security games in the interactive theorem prover Isabelle/HOL. Furthermore, we instantiate two PCS constructions, the standard DL-based KZG and a batched KZG version.

We define five abstract games against an adversary, covering correctness, the standard security properties for polynomial commitment schemes and desirable properties for SNARK construction:
-  __Correctness__
      Honest verifier and honest committer interaction. Formally, a Probability Massfuntion (PMF) over the probability of acceptance by the verifier.
- __Polynomial Binding__
      The adversary outputs one commitment to two distinct polynomials $\phi$ and $\phi'$ with according witnesses. The result is a PMF capturing the event that the verifier accepts both polynomials for the commitment. 
- __Evaluation Binding__
      The adversary outputs two distinct evaluation pairs $(\phi(i),i)$ and $(\phi(i)',i)$ to a commitment $C$ ($i$ and $C$ being chosen and fixed by the adversary) with according witnesses. The result is a PMF capturing the event that the verifier accepts the two distinct evaluations for the polynomial commitment.
- __Hiding__
      For an arbitrary but fixed polynomial $\phi$ of degree $d$, given $d$ evaluations of $\phi$, the adversary outputs a polynomial. The result is a PMF over the equality of the adversary's output polynomial and $\phi$.
- __Knowledge Soundness__
      Sometimes referred to as extractability \cite{thalerbook,SNARGsbook}. Intuitively this property states, that an adversary must know a polynomial $\phi$ and compute the commitment $C$ for $\phi$ honestly, to reveal points. 
      This game takes an extractor algorithm $E$ as input. The adversary outputs a commitment. The extractor, given access to the commitment then outputs an polynomial $p$ and a trapdoor value $td$ for the commitment. Then the adversary outputs the evaluation pair $(i,\phi(i))$ and according witness. 
      The result is a PMF capturing the event that the verifier accepts the adversary's outputs, but the adversary's evaluation does not match the extractor's evaluation (i.e. Eval applied to $i$ and the extractors polynomial $p$ and trapdoor $td$).

## Formal Verification of the KZG
The non-hiding DL-version of the KZG described in [KZG10]. We formally verify correctness, polynomial binding, evaluation binding, knowledge soundness, and a weaker version of hiding that is only hiding for uniform random polynomials. 

## Formal Verifrication of a batched KZG
The batched version is an extension of the KZG for two more functions, which allow to evaluate a degree $d$ polynomial at up to $d$ points with one witness and one pairing check. We formally verify correctness, polynomial binding, evaluation binding, and knowledge soundness.






