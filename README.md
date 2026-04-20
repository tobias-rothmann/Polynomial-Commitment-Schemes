# Polynomial Commitment Schemes in Isabelle/HOL


## Abstract 
We formalize the notion of polynomial commitment schemes (PCSs) in the proof assistant Isabelle/HOL and formally verify the security proofs of two variants of the widely popular Kate, Zaverucha, and Goldberg (KZG) construction. Moreover, we formalize the Algebraic Group Model (AGM) by Fuchsbauer, Klitz, and Loss using a novel constraint-programming-inspired approach. We formalize a reusable abstract definition of polynomial commitment schemes and define games for correctness, binding, hiding, and knowledge soundness/extractability. Based on this, we verify all applicable security proofs for two concrete PCS constructions: the standard (DL-)KZG and a batched KZG, using our AGM formalization in the knowledge-soundness proofs. Our proofs follow Shoup’s sequence-of-games approach, with machine-checked transitions, and are carried out in the CryptHOL framework for formal verification of cryptography in Isabelle. To our knowledge, this work is the first formalization of polynomial commitment schemes, the first formalization of the AGM, and the first formal verification of the security proofs for any concrete polynomial commitment scheme. This work lays the foundation for the formal verification of advanced cryptographic constructions, such as pairing-based zero-knowledge proofs (ZKPs) and succinct arguments.

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

## Formalization of the AGM
We provide the first general-purpose formalization of the Algebraic Group Model (AGM) by Fuchsbauer, Kiltz, and Loss in the Isabelle/HOL proof assistant. Our approach is inspired by constraint programming: instead of embedding the AGM via oracles, we guard every adversary call with an assertion that enforces the algebraic-algorithm rules—requiring each output group element to be accompanied by a creation vector over all previously seen group elements. The formalization decomposes assertion generation into three composable concerns: Select (collecting seen group elements from the input), Constrain (checking the AGM rules on the output), and Restrict (combining both into an enforceable assert). We provide combinators for compound types (lists, products, trees, multisets, finite sets, finite maps), enabling semi-automatic generation of AGM guards for adversaries with complex input/output types. The formalization is compatible with CryptHOL's SPMF monad, lifting seamlessly to the random oracle model and generalizing to other algebraic models such as the Algebraic Isogeny Model (AIM) or Algebraic Group Action Model (AGAM). We use this AGM formalization to formally verify knowledge soundness for both the standard and batched KZG.

## Formal Verification of the KZG
The non-hiding DL-version of the KZG described in [KZG10]. We formally verify __correctness__, __polynomial binding__, __evaluation binding__, __knowledge soundness__, and a weaker version of hiding, __weak hiding__, that is only hiding for uniform random polynomials. 

## Formal Verifrication of a batched KZG
The batched version is an extension of the KZG for two more functions, which allow to evaluate a degree $d$ polynomial at up to $d$ points with one witness and one pairing check. We formally verify __correctness__, __polynomial binding__, __evaluation binding__, and __knowledge soundness__.





