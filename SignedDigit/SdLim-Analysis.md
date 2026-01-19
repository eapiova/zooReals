# Direct Coinductive SdLim Proof: Analysis

This document analyzes whether implementing a direct coinductive proof of the signed-digit limit theorem (SdLim) makes sense for the Cubical Agda project.

## Background

The WK22 paper ("Limits of Real Numbers in the Binary Signed Digit Representation" by Wiesnet & Köpp) proves the **SdLim theorem**:

> For a sequence `xs : ℕ → ℝ` of reals in `coI` (signed-digit representable) converging to `x` with modulus `M`, we have `x ∈ coI`.

The paper provides two approaches:
1. **Direct**: Coinductive proof using the `coI⁺` axiom
2. **Indirect**: Via translations `StrToCs` and `CsToStr` between signed-digit and Cauchy representations

---

## Arguments FOR a Direct SdLim Proof

### 1. Computational Efficiency

WK22 benchmarks show significant differences:

| Approach | Lookahead for n digits |
|----------|------------------------|
| **Direct** | `3n` digits of `F(M(n+3))` — **linear** |
| **Indirect** | `M(n+4)` digits of `F(M(n+4))` — **quadratic in M** |

For modulus `M(p) = p`:
- Direct: 200 digits in ~87 seconds
- Indirect: 100 digits in ~1140 seconds (with `M(p) = p²`)

If the goal is to extract efficient algorithms, the direct proof produces better code.

### 2. Self-Contained Signed-Digit Theory

A direct proof would show that `𝕀sd` (or `ℝsd`) is **complete as a metric space** without relying on the HIT `lim` constructor. This enables:

- Working with streams independently of the Cauchy reals HIT
- Proving properties about stream transformations directly
- Future extraction to Haskell/other languages with cleaner results

### 3. Building Blocks for Signed-Digit Arithmetic

The direct proof in WK22 depends on several foundational lemmas:

| Lemma | Description | Current Agda Status |
|-------|-------------|---------------------|
| `CoIToCoIDouble` | `\|x\| ≤ 1/2 → 2x ∈ coI` | Not implemented |
| `CoINegToCoIPlusOne` | `x ≤ 0 → (x+1) ∈ coI` | Not implemented |
| `CoIPosToCoIMinusOne` | `0 ≤ x → (x-1) ∈ coI` | Not implemented |
| `CoIAverage` | `(x+y)/2 ∈ coI` | Not implemented |
| `TripleCases` | Case analysis on first 3 digits | Not implemented |

These are foundational for signed-digit arithmetic beyond just limits. Implementing them would enable:
- `CoIDiv` (division)
- `CoIMult` (multiplication)
- `sqrt` via Heron's method (as in WK22 Section 4.1)

### 4. Independence from Equivalence Proof

Currently, the project aims to prove `ℝsd ≃ ℝ`. Once proven, limits are "free":

```agda
sdLim : (s : ℕ → ℝsd) → Cauchy (toℝ ∘ s) → ℝsd
sdLim s p = fromℝ (lim (toℝ ∘ s) p)
```

However, this relies on:
1. The equivalence proof being complete (currently has holes)
2. Going through the HIT structure (potentially inefficient)

A direct proof provides an alternative path that doesn't depend on completing the equivalence.

---

## Arguments AGAINST a Direct SdLim Proof

### 1. Redundancy with Type Equivalence

If `ℝsd ≃ ℝ` is proven, limits are automatically handled:

```agda
-- The equivalence gives us this for free
fromℝ ∘ lim : (s : ℕ → ℝ) → Cauchy s → ℝsd
```

The limit construction is "baked into" the HoTT Cauchy reals HIT, so proving SdLim separately doesn't add new capability.

### 2. Significant Implementation Effort

The direct proof requires multiple supporting lemmas:

- `TripleCases` alone has **17 case distinctions**
- `CoIToCoIDouble` requires `CoINegToCoIPlusOne` and `CoIPosToCoIMinusOne`
- Each lemma needs careful reasoning about interval bounds

Estimated effort: Several hundred lines of Agda code.

### 3. Different Coinduction Mechanism

WK22 uses Minlog's `coI⁺` axiom (greatest fixed point):

```
coI⁺ : X ⊆ Φ(coI ∪ X) → X ⊆ coI
```

Cubical Agda uses:
- `Stream` type with guarded recursion
- Set quotients for `𝕀sd`

Translating the proof would require adapting to Cubical's coinduction patterns, which may not preserve the same computational behavior.

### 4. Focus Dilution

The current project has incomplete proofs in:
- `Equivalence.agda` (several holes in `Elimℝ-Prop` approach)
- `Bounded.agda` (some postulates)

Adding SdLim before completing these core goals spreads effort thin.

---

## Recommendations

### For Current Project Goals (proving `ℝsd ≃ ℝ`)

**Not necessary.** The `Elimℝ-Prop` surjectivity approach is cleaner and requires less machinery.

### For a Complete Signed-Digit Arithmetic Library

**Yes, valuable.** The building blocks (`CoIAverage`, `CoIDiv`, `CoIMult`) are useful independently, and WK22's benchmarks demonstrate the direct method's performance advantage.

### Suggested Middle Path

Implement the key building blocks first:

```agda
-- Stage 1: Basic operations (useful regardless of SdLim)
average : 𝕀sd → 𝕀sd → 𝕀sd      -- (x + y) / 2
double  : 𝕀sd → 𝕀sd             -- 2x for |x| ≤ 1/2
shift   : Digit → 𝕀sd → 𝕀sd     -- (d + x) / 2

-- Stage 2: Arithmetic
multiply : 𝕀sd → 𝕀sd → 𝕀sd
divide   : 𝕀sd → 𝕀sd → 𝕀sd     -- with bounds

-- Stage 3: Completeness
sdLim-direct : (s : ℕ → 𝕀sd) → Modulus → 𝕀sd
```

Once Stage 1-2 exist, SdLim becomes a natural addition. Without them, a standalone SdLim proof is harder to justify.

---

## References

- **WK22**: Wiesnet & Köpp, "Limits of Real Numbers in the Binary Signed Digit Representation" (2022)
  - Available in this directory: `WK22.pdf`, `2103.15702.pdf`
- **Agda Implementation**: `src/Reals/SignedDigit/`
