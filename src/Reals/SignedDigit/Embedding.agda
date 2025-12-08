{-# OPTIONS --cubical --guardedness #-}
-- NOTE: --safe is not used here because we postulate the Cauchy property for now.
-- TODO: Fill in proofs and restore --safe.

-- Embedding of Signed-Digit Reals into HoTT Cauchy Reals
-- 
-- This module constructs the embedding ι : ℝsd → ℝ
-- 
-- The key idea: a signed-digit stream s : 𝟛ᴺ represents a real number
-- via its approximation sequence approx(s, n) : ℚ. This sequence is
-- Cauchy, so we can use `lim` to embed it into the HoTT reals.

module Reals.SignedDigit.Embedding where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat as ℕ using (ℕ; zero; suc)
open import Cubical.Data.Int as ℤ using (ℤ; pos; negsuc)
open import Cubical.Data.Int.Fast.Properties as ℤᶠ using (·≡·f)
open import Cubical.Data.Sigma
open import Cubical.Data.NatPlusOne

open import Cubical.Data.Rationals.Base as ℚᵇ renaming (ℚ to ℚˢ)
open import Cubical.Data.Rationals.Fast as ℚ hiding ([_])
open import Cubical.Data.Rationals.Fast.Order as ℚO using (ℚ₊; _ℚ₊+_; 0<_; _<_; _≤_; _≟_; Trichotomy; lt; eq; gt)

open import Cubical.HITs.SetQuotients as SQ hiding ([_])

open import Reals.SignedDigit.Base
open import Reals.SignedDigit.Equivalence using (ℝsd; _≈sd_; isSetℝsd; 0sd; 1sd; -1sd; approx; inv2^; tail-bound-sym; 2^ℕ₊₁)
open import Reals.HoTT.Base using (ℝ; rat; lim; _∼[_]_; rat-rat-fromAbs)
open import Cubical.HITs.CauchyReals.Closeness using (isSetℝ; refl∼)

-- | Absolute value of 0 is 0 for Fast rationals
abs0 : ℚ.abs 0 ≡ 0
abs0 = ℚ.maxIdem 0

------------------------------------------------------------------------
-- Modulus computation: finding n such that 1/2^{n+1} < ε
------------------------------------------------------------------------

-- 2 as a Fast rational
2ℚ : ℚ.ℚ
2ℚ = ℚ.[ pos 2 / 1+ 0 ]

-- 1 as a Fast rational
1ℚ : ℚ.ℚ
1ℚ = ℚ.[ pos 1 / 1+ 0 ]

-- Helper: find smallest n such that q · 2^n ≥ 1
-- We multiply q by 2 repeatedly until it reaches or exceeds 1
-- The fuel parameter ensures termination
find-n-fuel : ℕ → ℚ.ℚ → ℕ
find-n-fuel zero _ = 0  -- fallback if we run out of fuel
find-n-fuel (suc fuel) q with 1ℚ ℚO.≟ q
... | lt _ = 0           -- q ≥ 1, we're done (need 0 more doublings)
... | eq _ = 0           -- q = 1, we're done
... | gt _ = suc (find-n-fuel fuel (2ℚ ℚ.· q))  -- q < 1, double and continue

-- Initial fuel: we use 1000 which is more than enough for any reasonable ε
-- (For ε = 2^{-n}, we need n iterations, and 2^1000 is astronomically large)
default-fuel : ℕ
default-fuel = 1000

-- --------------------------------------------------------------------------
-- Convert our approximations to Fast rationals
-- --------------------------------------------------------------------------

-- The approx function from Equivalence uses the regular ℚ.
-- We need to convert to Fast ℚ for the HoTT reals.
ℚˢ→ℚ : ℚˢ → ℚ.ℚ
ℚˢ→ℚ = SQ.rec ℚ.isSetℚ (λ { (a , b) → ℚ.[_/_] a b }) compat
  where
    toFast-rel : (x y : ℤ × ℕ₊₁) → ℚᵇ._∼_ x y → ℚ._∼_ x y
    toFast-rel (a , b) (c , d) rel =
      sym (ℤᶠ.·≡·f a (ℚ.ℕ₊₁→ℤ d)) ∙ rel ∙ ℤᶠ.·≡·f c (ℚ.ℕ₊₁→ℤ b)

    compat : (x y : ℤ × ℕ₊₁) → ℚᵇ._∼_ x y → ℚ.[_/_] (fst x) (snd x) ≡ ℚ.[_/_] (fst y) (snd y)
    compat (a , b) (c , d) rel = ℚ.eq/ (a , b) (c , d) (toFast-rel (a , b) (c , d) rel)

approxF : 𝟛ᴺ → ℕ → ℚ.ℚ  -- Approximation using Fast rationals
approxF s n = ℚˢ→ℚ (approx s n)

-- Convert a positive rational precision to a natural number
-- (compute how many digits we need for that precision)
-- We need n such that 1/2^{n+1} ≤ ε, i.e., 2^{n+1} ≥ 1/ε
-- This means 2 · 2^n ≥ 1/ε, so 2^n ≥ 1/(2ε)
-- We find n = find-n-fuel(ε) which gives us ε · 2^n ≥ 1
ℚ₊→ℕ : ℚ₊ → ℕ
ℚ₊→ℕ (ε , _) = find-n-fuel default-fuel ε

-- Given a stream, produce approximations indexed by ℚ₊ using the modulus
approxℚ₊ : 𝟛ᴺ → ℚ₊ → ℚ.ℚ
approxℚ₊ s ε = approxF s (ℚ₊→ℕ ε)

-- --------------------------------------------------------------------------
-- Embedding a single stream into ℝ
-- --------------------------------------------------------------------------

-- The approximation sequence is Cauchy
-- This requires showing that |approx s m - approx s n| ≤ 2^{-min(m,n)}
-- and that our modulus ℚ₊→ℕ ensures this bound is within the precision
-- In the current development we postulate this Cauchy property; a
-- constructive proof will later use the tail-bound lemmas from
-- Reals.SignedDigit.Equivalence.
postulate
  approxℚ₊-cauchy : (s : 𝟛ᴺ)
    → ∀ (δ ε : ℚ₊) → rat (approxℚ₊ s δ) ∼[ δ ℚ₊+ ε ] rat (approxℚ₊ s ε)

-- Embed a stream into the HoTT reals using the first partial sum
-- (placeholder; see `stream→ℝ-lim` below for the `lim`-based version)
stream→ℝ : 𝟛ᴺ → ℝ
stream→ℝ s = rat (approxF s 0)

-- Alternative: embed a stream via the Cauchy limit of its ℚ₊-indexed
-- approximations. This is the intended final construction of ι; the
-- code above still uses the simpler placeholder definition for now.
stream→ℝ-lim : 𝟛ᴺ → ℝ
stream→ℝ-lim s = lim (λ ε → rat (approxℚ₊ s ε)) (approxℚ₊-cauchy s)

-- --------------------------------------------------------------------------
-- The embedding respects the equivalence relation
-- --------------------------------------------------------------------------

-- Two ≈sd-equivalent streams map to equal reals
stream→ℝ-resp : ∀ s t → s ≈sd t → stream→ℝ s ≡ stream→ℝ t
stream→ℝ-resp s t h = cong rat (cong ℚˢ→ℚ (h 0))

-- --------------------------------------------------------------------------
-- ℝ is a set (required for quotient elimination)

-- Embedding from signed-digit reals to HoTT Cauchy reals
ι : ℝsd → ℝ
ι = SQ.rec isSetℝ stream→ℝ stream→ℝ-resp
