{-# OPTIONS --cubical --guardedness #-}

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
open import Reals.SignedDigit.Equivalence using (ℝsd; _≈sd_; isSetℝsd; 0sd; 1sd; -1sd; approx; inv2^; tail-bound-sym; 2^ℕ₊₁; stream→ℝ; approxℚ₊; approxℚ₊-cauchy)
open import Reals.HoTT.Base using (ℝ; rat; lim; _∼[_]_; rat-rat-fromAbs)
open import Cubical.HITs.CauchyReals.Closeness using (isSetℝ; refl∼)

-- | Absolute value of 0 is 0 for Fast rationals
abs0 : ℚ.abs 0 ≡ 0
abs0 = ℚ.maxIdem 0

-- --------------------------------------------------------------------------
-- Convert our approximations to Fast rationals
-- --------------------------------------------------------------------------

-- Since approx in Equivalence.agda now returns Fast ℚ directly,
-- approxF is just an alias for approx
approxF : 𝟛ᴺ → ℕ → ℚ.ℚ
approxF = approx

-- approxℚ₊ and ℚ₊→ℕ are imported from Equivalence.agda

-- --------------------------------------------------------------------------
-- Embedding a single stream into ℝ
-- --------------------------------------------------------------------------

-- stream→ℝ and approxℚ₊-cauchy are imported from Equivalence.agda
-- stream→ℝ s = lim (λ ε → rat (approxℚ₊ s ε)) (approxℚ₊-cauchy s)

-- Alternative name for backwards compatibility
stream→ℝ-lim : 𝟛ᴺ → ℝ
stream→ℝ-lim = stream→ℝ

-- --------------------------------------------------------------------------
-- The embedding respects the equivalence relation
-- --------------------------------------------------------------------------

-- Two ≈sd-equivalent streams map to equal reals.
-- With the new ≈sd definition (s ≈sd t = stream→ℝ s ≡ stream→ℝ t),
-- this is trivially the identity.
stream→ℝ-resp : ∀ s t → s ≈sd t → stream→ℝ s ≡ stream→ℝ t
stream→ℝ-resp s t h = h

-- --------------------------------------------------------------------------
-- ℝ is a set (required for quotient elimination)

-- Embedding from signed-digit reals to HoTT Cauchy reals
ι : ℝsd → ℝ
ι = SQ.rec isSetℝ stream→ℝ stream→ℝ-resp
