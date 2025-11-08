# zooReals

A Cubical Agda library implementing various constructions of real numbers and exploring their relationships.

## Overview

This project implements and compares different constructions of real numbers in Cubical Agda:

1. **Dedekind reals** - Constructed as cuts of rational numbers
2. **Cauchy reals** - Constructed as equivalence classes of Cauchy sequences
3. **Interval-based reals** - Using the interval constructor from cubical type theory

The project explores:
- Definitions and basic properties of each real number type
- Embeddings between different constructions
- Equivalences (or lack thereof) between constructions
- Counterexamples showing differences between constructions
- Computational properties of each construction

## Implemented Real Number Types

### Dedekind Reals
Dedekind reals are implemented as cuts of rational numbers. A Dedekind cut is a pair of predicates (L, R) on rationals satisfying:
- Separation: For all rationals p, q, if p < q and q ∈ R, then p ∈ L
- Roundoff: For all rationals p ∈ L, there exists q ∈ L with p < q, and for all rationals q ∈ R, there exists p ∈ R with p < q
- Locatedness: For all rationals p < q, either p ∈ L or q ∈ R

The implementation can be found in `src/Reals/Dedekind/Basic.agda`.

### Cauchy Reals
Cauchy reals are constructed as equivalence classes of Cauchy sequences. A Cauchy sequence is a sequence of rationals such that for all n, |x_m - x_k| < 2^(-n) for all m,k >= n.

Two sequences are equivalent if they converge to the same limit: for all n, there exists N such that for all m >= N, |x_m - y_m| < 2^(-n).

The implementation can be found in `src/Reals/Cauchy/Basic.agda`.

### Interval-based Reals
Interval-based reals use the interval constructor from cubical type theory. This approach leverages the computational properties of the cubical library.

## Embeddings and Equivalences

The project implements embeddings between different constructions of real numbers:

- Embedding from rationals to Dedekind reals
- Embedding from rationals to Cauchy reals
- Embedding from Cauchy reals to Dedekind reals
- Embedding from Dedekind reals to Cauchy reals

These embeddings are proven to be equivalences under appropriate choice principles, showing that the different constructions are equivalent types in Cubical Agda.

The implementations can be found in:
- `src/Reals/Embeddings.agda` - Defines the embeddings
- `src/Reals/Equivalences.agda` - Proves the equivalences

## Counterexamples

The project includes various counterexamples that demonstrate differences between classical and constructive mathematics when working with real numbers:

1. Functions that are pointwise continuous but not uniformly continuous
2. Sets that are not decidable
3. Cauchy sequences without constructive limits
4. Failures of classical theorems without additional assumptions
5. Non-constructive existence proofs that don't provide witnesses

These counterexamples illustrate the fundamental differences between classical and constructive mathematics when working with real numbers in Cubical Agda.

Implementation can be found in `src/Reals/Counterexamples.agda`.

## Directory Structure

See [directory-structure.md](directory-structure.md) for details on the project organization.

## Prerequisites

- Agda >= 2.6.0
- cubical library

## Installation

1. Clone this repository
2. Make sure the cubical library is installed and accessible to Agda
3. Add this library to your Agda configuration

## Usage

To compile and check the Agda code:

```bash
agda src/Reals/Base.agda
```

To typecheck a specific module:

```bash
agda src/Reals/Cauchy/Basic.agda
```

## Documentation

See the `doc/` directory for detailed documentation.

## Contributing

Contributions are welcome! Please feel free to submit pull requests or open issues for bugs and feature requests.

## License

This project is licensed under the MIT License - see the LICENSE file for details.