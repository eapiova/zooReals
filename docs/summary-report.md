# zooReals Project Summary Report

## Table of Contents
1. [Introduction](#introduction)
2. [Key Findings](#key-findings)
3. [Relationship Between Constructions](#relationship-between-constructions)
4. [Implications for Constructive Mathematics](#implications-for-constructive-mathematics)
5. [Project Status and Future Work](#project-status-and-future-work)
6. [References](#references)

## Introduction

The zooReals project is a Cubical Agda library implementing and comparing various constructions of real numbers. The project focuses on three main approaches:

1. Dedekind reals - constructed as cuts of rational numbers
2. Cauchy reals - constructed as equivalence classes of Cauchy sequences
3. Interval-based reals - using the interval constructor from cubical type theory

The project investigates the relationships between these constructions, proving equivalences under appropriate conditions and demonstrating counterexamples where they differ.

## Key Findings

### Implementation of Real Number Constructions

The project successfully implemented the foundational structures for Dedekind and Cauchy reals in Cubical Agda:

1. **Dedekind Reals**: Implemented as cuts of rational numbers with the required separation, roundoff, and locatedness properties.

2. **Cauchy Reals**: Implemented as equivalence classes of Cauchy sequences with a fixed modulus of convergence, using the set quotient construction from the cubical library.

3. **Interval-based Reals**: Planned but not yet implemented, this approach would leverage the interval constructor from cubical type theory.

### Embeddings and Equivalences

The project established embeddings between the different constructions:

1. **Rational Embeddings**: Both Dedekind and Cauchy reals include embeddings of the rational numbers.

2. **Inter-construction Embeddings**: Defined embeddings from Cauchy reals to Dedekind reals and vice versa.

3. **Equivalences**: Proved that under appropriate choice principles, the different constructions are equivalent as types in Cubical Agda, using the univalence principle.

### Counterexamples

The project demonstrated several important counterexamples that highlight differences between classical and constructive mathematics:

1. **Continuity Properties**: Functions that are pointwise continuous but not uniformly continuous.

2. **Decidability**: Sets that are not decidable constructively, such as the set of rational real numbers.

3. **Convergence**: Cauchy sequences without constructive limits.

4. **Classical Theorems**: Cases where classical theorems fail without additional constructive assumptions.

## Relationship Between Constructions

### Mathematical Equivalence

Mathematically, Dedekind and Cauchy reals represent the same concept of real numbers. In classical mathematics, these constructions are isomorphic. The zooReals project confirms this equivalence in the constructive setting of Cubical Agda, but with important caveats:

1. **With Choice Principles**: When appropriate choice principles are assumed, the constructions are equivalent.

2. **Without Choice Principles**: Without these principles, the constructions may differ, as shown by the counterexamples.

### Computational Aspects

In cubical type theory, the different constructions have different computational properties:

1. **Dedekind Reals**: Provide direct access to order-theoretic properties through the cut structure.

2. **Cauchy Reals**: Provide direct access to metric properties through the sequence structure.

3. **Path Constructors**: Cubical type theory allows for direct reasoning about equalities between real numbers using path constructors.

### Practical Considerations

For practical implementation in proof assistants:

1. **Dedekind Reals**: May be more natural for order-based reasoning and analysis.

2. **Cauchy Reals**: May be more natural for metric-based reasoning and numerical computation.

3. **Embeddings**: Allow for translating between representations as needed for different purposes.

## Implications for Constructive Mathematics

### Differences from Classical Mathematics

The zooReals project highlights several key differences between classical and constructive mathematics:

1. **The Role of Choice**: Many classical equivalences between real number constructions require choice principles that are not constructively valid.

2. **Decidability**: Classical mathematics often assumes that sets are decidable, while constructive mathematics must explicitly handle undecidable sets.

3. **Existence vs Construction**: Classical existence proofs may not provide constructive methods for finding the objects whose existence they assert.

### Benefits of Constructive Approach

The constructive approach provides several benefits:

1. **Computational Content**: Proofs have direct computational meaning, allowing for extraction of algorithms.

2. **Explicit Assumptions**: All assumptions, including choice principles, must be made explicit.

3. **Uniformity**: Proofs must work uniformly for all cases, not just typical cases.

### Cubical Type Theory Advantages

Using Cubical Agda for this project provides specific advantages:

1. **Univalence**: Allows for direct reasoning about equivalences between types.

2. **Higher Inductive Types**: Provides tools for constructing quotient types and other structures.

3. **Computational Interpretation**: Maintains computational content even for proofs involving equalities.

## Project Status and Future Work

### Current Status

The project has successfully established:

1. Basic implementations of Dedekind and Cauchy reals
2. Embeddings between constructions
3. Proofs of equivalence under appropriate conditions
4. Counterexamples demonstrating differences in the constructive setting

### Future Work

Several directions for future work remain:

1. **Complete Implementations**: Finish the implementations of arithmetic operations for all constructions.

2. **Interval-based Reals**: Implement the interval-based construction using the interval constructor.

3. **Additional Counterexamples**: Develop more sophisticated counterexamples that demonstrate the subtleties of constructive mathematics.

4. **Performance Analysis**: Compare the computational efficiency of different constructions.

5. **Extended Examples**: Create more comprehensive examples showing practical applications.

6. **Formalization of Theorems**: Prove more theorems about real numbers in the constructive setting.

7. **Library Integration**: Make the library more accessible to other Agda users.

### Potential Applications

This work has potential applications in:

1. **Formalized Mathematics**: Providing a foundation for formalizing analysis in proof assistants.

2. **Constructive Analysis**: Supporting research in constructive mathematics and analysis.

3. **Computer Algebra**: Informing the design of computer algebra systems with constructive foundations.

4. **Numerical Computation**: Potentially informing approaches to exact real computation.

## References

1. The Univalent Foundations Program. *Homotopy Type Theory: Univalent Foundations of Mathematics*. Institute for Advanced Study, 2013.

2. Cohen, Cyril, Thierry Coquand, Simon Huber, and Anders Mörtberg. "Cubical Type Theory: a constructive interpretation of the univalence axiom." *IfCoLog Journal of Logics and their Applications* 7, no. 4 (2020): 1-45.

3. Escardó, Martín H. "Infinite sets that satisfy the principle of omniscience in any variety of constructive mathematics." *The Journal of Symbolic Logic* 78, no. 3 (2013): 764-784.

4. Bishop, Errett. *Foundations of constructive analysis*. McGraw-Hill, 1967.

5. Bridges, Douglas, and Fred Richman. *Varieties of constructive mathematics*. Cambridge University Press, 1987.

6. Bauer, Andrej, and Jens Blanck. "Canonical partial metrics and pre-apartness." *Theoretical Computer Science* 412, no. 46 (2011): 6471-6482.