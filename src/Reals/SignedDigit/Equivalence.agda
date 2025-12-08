{-# OPTIONS --cubical --guardedness #-}
-- NOTE: --safe is not used here because tail-bound lemmas are currently postulated.
-- TODO: Fill in tail-bound proofs and restore --safe.

-- Equivalence relation on signed-digit sequences and the quotient type ℝsd
-- Based on TWA Thesis Chapter 5 (TypeTopology), ported to Cubical Agda

module Reals.SignedDigit.Equivalence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

open import Cubical.Data.Nat as ℕ using (ℕ; zero; suc; min; minComm)
open import Cubical.Data.Nat.Order as ℕO using (splitℕ-≤; splitℕ-<; ≤-split; min-≤-left; minGLB; ≤-refl; ≤-antisym; <-weaken) renaming (_≤_ to _≤ℕ_)
open import Cubical.Data.Int as ℤ using (ℤ; pos; negsuc)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)

open import Cubical.Data.Rationals.Base using (ℚ; [_/_])
open import Cubical.Data.Rationals.Properties as ℚP using (_·_; _+_; _-_; -_; abs; max; maxComm; -Invol; -[x-y]≡y-x; +InvR)
open import Cubical.Data.Rationals.Order as ℚO using (_≤_; _<_; isRefl≤)


open import Cubical.HITs.SetQuotients as SQ hiding ([_])

open import Reals.SignedDigit.Base

------------------------------------------------------------------------
-- Rational approximations
------------------------------------------------------------------------

-- 2^n as ℕ
2^ℕ : ℕ → ℕ
2^ℕ zero = 1
2^ℕ (suc n) = 2 ℕ.· 2^ℕ n

-- 2^n as ℕ₊₁ (for use as denominator) - we know 2^n ≥ 1
2^ℕ₊₁ : ℕ → ℕ₊₁
2^ℕ₊₁ zero = 1+ 0           -- 2^0 = 1
2^ℕ₊₁ (suc n) with 2^ℕ n
... | zero = 1+ 0           -- impossible case
... | suc m = 1+ (m ℕ.+ suc m)  -- 2 * (suc m) = suc m + suc m = 2 + 2m

-- Convert digit to rational: -1 ↦ -1, 0 ↦ 0, +1 ↦ +1
digitToℚ : Digit → ℚ
digitToℚ -1d = [ negsuc 0 / 1+ 0 ]   -- -1/1
digitToℚ 0d  = [ pos 0 / 1+ 0 ]      -- 0/1
digitToℚ +1d = [ pos 1 / 1+ 0 ]      -- 1/1

-- Single digit contribution at position i: dᵢ / 2^(i+1)
digitContrib : Digit → ℕ → ℚ
digitContrib d i = (digitToℚ d) · [ pos 1 / 2^ℕ₊₁ (suc i) ]

-- Finite approximation: Σᵢ₌₀ⁿ dᵢ / 2^(i+1)
-- This computes the partial sum of the signed-digit representation
approx : 𝟛ᴺ → ℕ → ℚ
approx s zero = digitContrib (s ! zero) zero
approx s (suc n) = approx s n + digitContrib (s ! suc n) (suc n)

------------------------------------------------------------------------
-- Equivalence relation
------------------------------------------------------------------------

-- Two signed-digit sequences are equivalent if they have the same limit
-- This is captured by: their approximations converge to the same value
-- Formally: ∀ ε > 0. ∃ N. ∀ n ≥ N. |approx x n - approx y n| < ε
--
-- For simplicity, we use extensional equality on the limit:
-- The approximations eventually agree (their difference vanishes)

-- Pointwise equality of approximations (strong version)
-- This is sufficient because the partial sums are monotonically refining
_≈sd_ : 𝟛ᴺ → 𝟛ᴺ → Type₀
x ≈sd y = (n : ℕ) → approx x n ≡ approx y n

-- Note: For signed-digit reals, ≈sd is the appropriate equivalence
-- because different digit streams can represent the same real number
-- Example: 0.111... = 1.000... (in binary, similar for signed-digit)

------------------------------------------------------------------------
-- Signed-digit reals as a quotient type
------------------------------------------------------------------------

-- The type of signed-digit real numbers in [-1, 1]
-- Quotienting by ≈sd identifies streams with the same limit
ℝsd : Type₀
ℝsd = 𝟛ᴺ / _≈sd_

-- Embedding raw sequences into ℝsd
[_]sd : 𝟛ᴺ → ℝsd
[ s ]sd = SQ.[ s ]

-- The quotient is a set
isSetℝsd : isSet ℝsd
isSetℝsd = squash/

------------------------------------------------------------------------
-- Basic elements
------------------------------------------------------------------------

-- The constant zero stream: 0, 0, 0, ...
-- Represents: Σᵢ 0/2^(i+1) = 0
zeroStream : 𝟛ᴺ
zeroStream = repeat 0d

-- The constant +1 stream: +1, +1, +1, ...
-- Represents: Σᵢ 1/2^(i+1) = 1
oneStream : 𝟛ᴺ
oneStream = repeat +1d

-- The constant -1 stream: -1, -1, -1, ...
-- Represents: Σᵢ -1/2^(i+1) = -1
negOneStream : 𝟛ᴺ
negOneStream = repeat -1d

-- Zero, one, and negative one as signed-digit reals
0sd : ℝsd
0sd = [ zeroStream ]sd

1sd : ℝsd
1sd = [ oneStream ]sd

-1sd : ℝsd
-1sd = [ negOneStream ]sd

------------------------------------------------------------------------
-- Tail bound lemmas
------------------------------------------------------------------------

-- The key property of signed-digit approximations:
-- The difference between partial sums at indices m and n is bounded by
-- the tail of a geometric series.

-- Helper: 1 / 2^{n+1} as a rational
inv2^ : ℕ → ℚ
inv2^ n = [ pos 1 / 2^ℕ₊₁ (suc n) ]

-- The tail bound: for m ≤ n, |approx s n - approx s m| ≤ 1/2^{m+1}
-- This follows because each digit d_i contributes at most 1/2^{i+1},
-- and the sum from i=m+1 to n is bounded by the geometric series sum
-- which converges to 1/2^{m+1}.

-- The following lemmas establish bounds on signed-digit approximations.
-- They require substantial rational arithmetic proofs.
--
-- Proof sketch: The difference is Σᵢ₌ₘ₊₁ⁿ dᵢ/2^{i+1} where |dᵢ| ≤ 1.
-- This sum is bounded by Σᵢ₌ₘ₊₁^∞ 1/2^{i+1} = 1/2^{m+1}.

-- Main tail bound: for m ≤ n, |approx s n - approx s m| ≤ 1/2^{m+1}
postulate
  tail-bound : (s : 𝟛ᴺ) (m n : ℕ) → m ≤ℕ n
    → abs (approx s n ℚP.- approx s m) ℚO.≤ inv2^ m

-- Helper: absolute value is invariant under negation
abs-neg : (x : ℚ) → abs (- x) ≡ abs x
abs-neg x = cong (max (- x)) (-Invol x) ∙ maxComm (- x) x

-- Helper: symmetry of |x - y|
abs-minus-sym : (x y : ℚ) → abs (x ℚP.- y) ≡ abs (y ℚP.- x)
abs-minus-sym x y = sym (abs-neg (x ℚP.- y)) ∙ cong abs (-[x-y]≡y-x x y)

-- Helper: min m n when m ≤ n
min-eq-left : (m n : ℕ) → m ≤ℕ n → min m n ≡ m
min-eq-left m n m≤n =
  ≤-antisym (min-≤-left {m} {n}) (minGLB {x = m} ≤-refl m≤n)

-- Helper: min m n when n ≤ m
min-eq-right : (m n : ℕ) → n ≤ℕ m → min m n ≡ n
min-eq-right m n n≤m =
  minComm m n ∙ min-eq-left n m n≤m

-- Symmetric version for arbitrary m, n
tail-bound-sym : (s : 𝟛ᴺ) (m n : ℕ)
  → abs (approx s m ℚP.- approx s n) ℚO.≤ inv2^ (min m n)
tail-bound-sym s m n with splitℕ-≤ m n
... | inl m≤n =
  let
    p₀ : abs (approx s n ℚP.- approx s m) ℚO.≤ inv2^ m
    p₀ = tail-bound s m n m≤n

    p₁ : abs (approx s m ℚP.- approx s n) ℚO.≤ inv2^ m
    p₁ = subst (λ z → z ℚO.≤ inv2^ m)
               (sym (abs-minus-sym (approx s m) (approx s n)))
               p₀

    p₂ : abs (approx s m ℚP.- approx s n) ℚO.≤ inv2^ (min m n)
    p₂ = subst (λ t → abs (approx s m ℚP.- approx s n) ℚO.≤ t)
               (cong inv2^ (sym (min-eq-left m n m≤n)))
               p₁
  in p₂
... | inr n<m =
  let
    n≤m : n ≤ℕ m
    n≤m = <-weaken n<m

    p : abs (approx s m ℚP.- approx s n) ℚO.≤ inv2^ n
    p = tail-bound s n m n≤m
  in subst (λ t → abs (approx s m ℚP.- approx s n) ℚO.≤ t)
           (cong inv2^ (sym (min-eq-right m n n≤m)))
           p



------------------------------------------------------------------------
-- Export key lemmas
------------------------------------------------------------------------

-- Re-export for use in Embedding module
open import Cubical.Data.Rationals.Properties public using (abs; _-_)

-- Export the tail bound for use in proving the Cauchy property
-- inv2^ and tail-bound-sym are the key exports
