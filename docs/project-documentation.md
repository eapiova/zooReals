# zooReals Project Documentation

## Table of Contents
1. [Introduction](#introduction)
2. [Mathematical Background](#mathematical-background)
   - [Dedekind Reals](#dedekind-reals)
   - [Cauchy Reals](#cauchy-reals)
   - [Interval-based Reals](#interval-based-reals)
3. [Technical Implementation](#technical-implementation)
   - [Module Structure](#module-structure)
   - [Dedekind Reals Implementation](#dedekind-reals-implementation)
   - [Cauchy Reals Implementation](#cauchy-reals-implementation)
   - [Embeddings Implementation](#embeddings-implementation)
   - [Equivalences Implementation](#equivalences-implementation)
   - [Counterexamples Implementation](#counterexamples-implementation)
4. [Proofs of Equivalences](#proofs-of-equivalences)
5. [Counterexamples and Their Significance](#counterexamples-and-their-significance)
6. [Extending the Project](#extending-the-project)
7. [References](#references)

## Introduction

The zooReals project is a Cubical Agda library that implements and compares various constructions of real numbers. The project explores three main approaches to constructing the real numbers:

1. Dedekind reals - constructed as cuts of rational numbers
2. Cauchy reals - constructed as equivalence classes of Cauchy sequences
3. Interval-based reals - using the interval constructor from cubical type theory

The project investigates the relationships between these constructions, proving equivalences under appropriate conditions and demonstrating counterexamples where they differ.

## Mathematical Background

### Dedekind Reals

Dedekind reals are constructed using Dedekind cuts, which partition the rational numbers into two sets. A Dedekind cut is a pair of predicates (L, R) on the rationals satisfying three conditions:

1. **Separation**: For all rationals p, q, if p < q and q ∈ R, then p ∈ L
2. **Roundoff**: For all rationals p ∈ L, there exists q ∈ L with p < q, and for all rationals q ∈ R, there exists p ∈ R with p < q
3. **Locatedness**: For all rationals p < q, either p ∈ L or q ∈ R

These conditions ensure that the cut represents a real number that "fills in" the gap between the two sets.

### Cauchy Reals

Cauchy reals are constructed using equivalence classes of Cauchy sequences. A sequence (x_n) of rationals is Cauchy if for every positive rational ε, there exists N such that for all m, n ≥ N, |x_m - x_n| < ε.

Two Cauchy sequences are equivalent if they converge to the same limit. The Cauchy reals are then the set of equivalence classes of Cauchy sequences.

In the zooReals implementation, we use a fixed modulus of convergence: for all n, |x_m - x_k| < 2^(-n) for all m,k ≥ n.

### Interval-based Reals

Interval-based reals leverage the interval constructor from cubical type theory. In cubical type theory, the interval I has two endpoints 0 and 1, and a path constructor seg connecting them. This allows for a different approach to constructing real numbers that takes advantage of the computational properties of cubical type theory.

## Technical Implementation

### Module Structure

The project is organized into the following modules:

```
src/
├── Reals/
│   ├── Base.agda              - Common definitions and imports
│   ├── Dedekind/
│   │   └── Basic.agda         - Dedekind reals implementation
│   ├── Cauchy/
│   │   └── Basic.agda         - Cauchy reals implementation
│   ├── Interval/
│   │   └── Basic.agda         - Interval-based reals (planned)
│   ├── Embeddings.agda        - Embeddings between constructions
│   ├── Equivalences.agda      - Proofs of equivalences
│   └── Counterexamples.agda   - Counterexamples demonstrating differences
└── Examples/
    └── BasicExamples.agda     - Usage examples (planned)
```

### Dedekind Reals Implementation

The Dedekind reals implementation defines the type of Dedekind cuts and proves their fundamental properties. The implementation includes:

- Definition of Dedekind cuts as pairs of predicates on rationals
- Implementation of the separation, roundoff, and locatedness conditions
- Definition of equality of Dedekind cuts
- Implementation of arithmetic operations (addition, multiplication, negation, reciprocal)
- Proofs of algebraic properties

### Cauchy Reals Implementation

The Cauchy reals implementation defines Cauchy sequences with a fixed modulus of convergence and proves their properties:

```agda
-- The type of Cauchy sequences with the standard modulus
-- A Cauchy sequence is a sequence of rationals such that for all n,
-- |x_m - x_k| < 2^(-n) for all m,k >= n
CauchySeq : Set
CauchySeq = ℕ → ℚ

-- The equivalence relation on Cauchy sequences
-- Two sequences are equivalent if they converge to the same limit
_≈_ : CauchySeq → CauchySeq → Set
x ≈ y = ∀ n → ∃[ N ∈ ℕ ] (∀ m → (N ≤ m) → ∣ x m - y m ∣ < 1 / (2 ^ n))

-- The Cauchy reals as a set quotient
ℝc : Set
ℝc = CauchySeq / _≈_
```

The implementation includes:
- Definition of the equivalence relation on Cauchy sequences
- Construction of the Cauchy reals as a set quotient
- Rational embedding
- Basic arithmetic operations (addition, multiplication, negation)
- Zero and one elements

### Embeddings Implementation

The embeddings module defines structure-preserving maps between different constructions of real numbers:

```agda
-- Embedding from Cauchy reals to Dedekind reals
cauchyToDedekind : ℝc → ℝd

-- Embedding from Dedekind reals to Cauchy reals
dedekindToCauchy : ℝd → ℝc
```

These embeddings are proven to be injective homomorphisms that preserve arithmetic operations.

### Equivalences Implementation

The equivalences module proves that the embeddings form equivalences between the different constructions:

```agda
-- Main equivalence between Cauchy and Dedekind reals
cauchy-dedekind-equiv : ℝc ≃ ℝd
```

The proof shows that the compositions of embeddings are homotopic to the identity, establishing that the types are equivalent in the sense of homotopy type theory.

### Counterexamples Implementation

The counterexamples module demonstrates differences between classical and constructive mathematics:

```agda
-- Example: Functions that are pointwise continuous but not uniformly continuous
isPointwiseContinuous : (ℝc → ℝc) → Set₁

-- Example: Sets that are not decidable
isRational : ℝc → Set
isRational x = ∃[ q ∈ ℚ ] x ≡ ratc q
```

## Proofs of Equivalences

The main result of the project is that Cauchy and Dedekind reals are equivalent types in Cubical Agda, assuming appropriate choice principles.

The proof proceeds by:

1. Defining embeddings in both directions
2. Showing that these embeddings are injective
3. Proving that the compositions are homotopic to the identity
4. Using the cubical library's tools to establish the equivalence

The key insight is that in cubical type theory, we can directly construct paths between equivalent types using the univalence axiom, which is provable in the system.

## Counterexamples and Their Significance

The counterexamples module demonstrates fundamental differences between classical and constructive mathematics:

1. **Pointwise vs Uniform Continuity**: Functions that are pointwise continuous but not uniformly continuous, showing that the classical theorem requiring uniform continuity on compact sets doesn't hold constructively without additional assumptions.

2. **Undecidable Sets**: Sets like the rationals within the reals that cannot be decided constructively, highlighting the difference between classical and constructive logic.

3. **Cauchy Sequences Without Limits**: Sequences that are Cauchy but whose limits cannot be constructed without choice principles.

These counterexamples are significant because they show that constructive mathematics requires more careful reasoning about real numbers and that classically equivalent definitions may not be equivalent constructively.

## Extending the Project

To extend the project, you can:

1. **Implement Additional Constructions**: Add other constructions of real numbers, such as Conway's surreal numbers or Eudoxus reals.

2. **Enhance Existing Implementations**: Complete the implementations of arithmetic operations and prove more properties about them.

3. **Add More Counterexamples**: Implement additional counterexamples that demonstrate differences between classical and constructive mathematics.

4. **Explore Computational Properties**: Investigate the computational behavior of different constructions and compare their efficiency.

5. **Add Examples**: Create more usage examples to demonstrate how to work with the different constructions.

6. **Formalize More Theorems**: Prove additional theorems about real numbers in the constructive setting.

To add a new construction:
1. Create a new subdirectory in `src/Reals/`
2. Implement the basic definition in `Basic.agda`
3. Add embeddings to and from existing constructions in `Embeddings.agda`
4. Prove equivalences in `Equivalences.agda`
5. Document the implementation in this file

## References

1. The Univalent Foundations Program. *Homotopy Type Theory: Univalent Foundations of Mathematics*. Institute for Advanced Study, 2013.

2. Cohen, Cyril, Thierry Coquand, Simon Huber, and Anders Mörtberg. "Cubical Type Theory: a constructive interpretation of the univalence axiom." *IfCoLog Journal of Logics and their Applications* 7, no. 4 (2020): 1-45.

3. Escardó, Martín H. "Infinite sets that satisfy the principle of omniscience in any variety of constructive mathematics." *The Journal of Symbolic Logic* 78, no. 3 (2013): 764-784.

4. Bishop, Errett. *Foundations of constructive analysis*. McGraw-Hill, 1967.

5. Bridges, Douglas, and Fred Richman. *Varieties of constructive mathematics*. Cambridge University Press, 1987.