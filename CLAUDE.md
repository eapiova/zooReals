# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

zooReals is a Cubical Agda library implementing and comparing multiple constructions of real numbers:
- **Dedekind reals** (`ℝd`) - Cuts of rationals with L/R predicates
- **Cauchy reals** (`ℝc`) - Equivalence classes of Cauchy sequences via set quotients
- **HoTT reals** - Using `Cubical.HITs.CauchyReals` from the cubical library
- **Signed-digit reals** (`𝟛ᴺ`) - Streams of ternary digits {-1, 0, +1} representing [-1, 1]

## Build Commands

```bash
# Typecheck a specific module
agda src/Reals/Base.agda

# Typecheck the main entry points
agda src/Reals/Dedekind/Basic.agda
agda src/Reals/Cauchy/Basic.agda
agda src/Reals/SignedDigit/Base.agda
```

## Library Configuration

The project uses `--cubical --guardedness` flags (defined in `zooReals.agda-lib`). It depends on the `cubical-cauchy` library variant of the cubical library.

## Code Architecture

### Core Module Hierarchy

```
src/Reals/
├── Base.agda              # Common imports, ℚ literals (0#, 1#, 2#)
├── Dedekind/Basic.agda    # DedekindCut record, ℝd type, ratd embedding
├── Cauchy/Basic.agda      # CauchySeq, _≈_ relation, ℝc quotient type, ratc embedding
├── SignedDigit/Base.agda  # Digit type, 𝟛ᴺ streams, ternary representation
├── HoTT/Base.agda         # Re-exports Cubical.HITs.CauchyReals.Base
├── Embeddings.agda        # cauchyToDedekind, dedekindToCauchy
├── Equivalences.agda      # Proofs that ℝc ≃ ℝd
└── Counterexamples.agda   # Constructive vs classical differences
```

### Key Type Definitions

- `DedekindCut` record: fields `L R : ℚ → Set` with properties (inhabited, disjoint, rounded, located, order-respecting)
- `CauchySeq = ℕ → ℚ` with `_≈_` equivalence relation
- `ℝc = CauchySeq / _≈_` (set quotient)
- `Digit` datatype: `-1d | 0d | +1d`
- `𝟛ᴺ = Stream Digit` (coinductive streams)

### Cubical Agda Patterns Used

- `Cubical.HITs.SetQuotients` for Cauchy reals quotient construction
- `Cubical.HITs.PropositionalTruncation` for existential witnesses in Dedekind cuts
- `Cubical.Codata.Stream` for signed-digit coinductive streams
- `Cubical.Foundations.Equiv` and `isoToIsEquiv` for type equivalences

## Work in Progress

Many proofs contain `{!!}` holes, particularly:
- Arithmetic operations on Dedekind reals (`_+d_`, `_*d_`, `-d_`)
- `dedekindToCauchy` embedding construction
- Equivalence proofs between constructions
- Various lemmas about rational arithmetic bounds
