# Formalizing the Kate-Zaverucha-Goldberg Polynomial Commitment Scheme

## Abstract

## Introduction 
* relevance: 
    * modern crypto -> SNARKs, Verkle Trees
    * Practice secure money -> Ethereum, Rollups, Identity

* contribution:
We formalize the following security properties for the DL-construction: 
    * polynomial-binding
    * evaluation biding 
    * hiding 
    * knowledge soundness
    * all of the above properteis for the BatchVersion

## related work

* Sigma Commit Crypto
* Groth16 Lean

## Preliminaries

### Math Background

#### Finite Fields

#### Cylcic groups

#### Pairings

### Crypto Background

#### Hardness assumptions

##### DL

##### t-SDH

#### Game-based proofs

#### Commitment Schemes

##### Polynomial Commitment schemes

### Isabelle 

#### CryptHOL

## The KZG

* explain whats the idea behind the KZG 
=> paring based zero-check

## Formalization of security properties

### (polynomial hiding?)

### evaluation binding

#### paper proof

#### formalization

### knowledge soundness

#### paper proof

#### formalization

### hiding

#### paper proof

#### formalization

## Batch Version of the KZG

* explain whats the idea behind batching 
=> constant size for arbitrary opening

## Formalization of the security properties for batching

#### paper proof

#### formalization

### batch-evalutaion binding

#### paper proof

#### formalization

### knowledge soundness

#### paper proof

#### formalization

### hiding

#### paper proof

#### formalization

## Conclusion

### Furture Work