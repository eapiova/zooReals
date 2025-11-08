# Embeddings, Equivalences, and Counterexamples

## Overview

This document describes the approach for exploring relationships between different constructions of real numbers in the zooReals project.

## Embeddings

An embedding from one real number construction to another is a structure-preserving map that is injective. We will explore:

### Dedekind to Cauchy
- Define a map from Dedekind cuts to equivalence classes of Cauchy sequences
- Show this map preserves arithmetic operations
- Prove injectivity

### Cauchy to Dedekind
- Define a map from equivalence classes of Cauchy sequences to Dedekind cuts
- Show this map preserves arithmetic operations
- Prove injectivity

## Equivalences

An equivalence between two constructions means there are embeddings in both directions that compose to the identity. We will investigate:

### Conditions for Equivalence
- In the presence of countable choice, Dedekind and Cauchy reals are equivalent
- Without choice principles, they may differ
- Explore what additional structure is needed for equivalence

### Proving Equivalence
- Construct explicit inverses for embeddings
- Show that compositions are homotopic to identity
- Use univalence from the cubical library where applicable

## Counterexamples

We will construct explicit examples showing where constructions differ:

### Without Choice Principles
- Models where Cauchy sequences don't converge to Dedekind cuts
- Situations where Dedekind completeness fails for Cauchy reals

### Computational Differences
- Examples showing different reduction behavior
- Cases where one construction computes more efficiently than another

## Approach in Cubical Type Theory

Using the cubical library, we can:

1. Use univalence to show equivalences between types
2. Construct higher inductive types for quotients
3. Reason about paths and equalities more directly
4. Explore computational behavior of constructions

## Specific Investigations

### 1. The Relationship Between Constructions
- When is the embedding from Dedekind to Cauchy reals an equivalence?
- What about the reverse direction?

### 2. Computational Content
- How do different constructions compute?
- Are there terms that have different normal forms in different constructions?

### 3. Topological Properties
- How do the different constructions relate to topological notions of completeness?
- What is the relationship to the interval constructor in cubical type theory?

### 4. Algebraic Properties
- Do all constructions satisfy the same algebraic laws?
- Are there additional properties that distinguish them?

## Implementation Strategy

1. First implement the basic constructions separately
2. Then define the embeddings between them
3. Prove properties about when these embeddings are equivalences
4. Finally construct explicit counterexamples showing differences