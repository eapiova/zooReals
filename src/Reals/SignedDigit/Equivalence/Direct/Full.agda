{-# OPTIONS --cubical --guardedness #-}

------------------------------------------------------------------------
-- Signed-Digit Equivalence: Full ℝsd ≃ ℝ
------------------------------------------------------------------------
--
-- This module builds the full equivalence ℝsd ≃ ℝ using:
--   - ι⁻¹ from Direct.Rec (cached)
--   - choose-k from Helpers
--   - Multiplication for toℝ
--
-- Separated from Direct.agda because Helpers.agda transitively
-- loads CauchyReals.Order and CauchyReals.Multiplication (~25GB RAM).
--
-- KEY EXPORTS:
--   fromℝ     : ℝ → ℝsd
--   ℝsd≃ℝ     : ℝsd ≃ ℝ
--   ℝsd≡ℝ     : ℝsd ≡ ℝ
--
------------------------------------------------------------------------

module Reals.SignedDigit.Equivalence.Direct.Full where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence

open import Cubical.Data.Int as ℤ using (ℤ; pos)
open import Cubical.HITs.SetQuotients as SQ hiding ([_])

open import Cubical.HITs.CauchyReals.Base as ℝBase using (ℝ; rat)
open import Cubical.HITs.CauchyReals.Multiplication as ℝMul using (_·ᵣ_)

open import Reals.SignedDigit.Core
open import Reals.SignedDigit.Bounded using (𝕀sd; _≈sd_; stream→ℝ)
open import Reals.SignedDigit.Representation using (ℝsd; toℝ; toℝ-raw; pow2ℤ; isSetℝsd)
open import Reals.SignedDigit.Equivalence.Helpers using (ℝ∈OpenUnit; val; choose-k)
open import Reals.SignedDigit.Equivalence.Direct.Rec using (ι⁻¹)

------------------------------------------------------------------------
-- Full Equivalence (ℝ → ℝsd)
------------------------------------------------------------------------

-- Helper to lift (k, s) to ℝsd respecting equivalence
lift-to-ℝsd : ℤ → 𝕀sd → ℝsd
lift-to-ℝsd k = SQ.rec isSetℝsd (λ s → SQ.[ (k , s) ]) coh
  where
    coh : (s t : 𝟛ᴺ) → s ≈sd t → SQ.[ (k , s) ] ≡ SQ.[ (k , t) ]
    coh s t h = SQ.eq/ (k , s) (k , t) path
      where
        path : toℝ-raw (k , s) ≡ toℝ-raw (k , t)
        path = cong (λ x → rat (pow2ℤ k) ·ᵣ x) h

-- Full encoding: use choose-k to get exponent and normalized value,
-- then embed the normalized value using ι⁻¹.
fromℝ : ℝ → ℝsd
fromℝ x with choose-k x
... | (k , z) = lift-to-ℝsd k (ι⁻¹ (val z))

------------------------------------------------------------------------
-- Round-trip properties (postulated)
------------------------------------------------------------------------

postulate
  -- TODO: Requires δ-correct and choose-k-correct
  toℝ-fromℝ : (y : ℝ) → toℝ (fromℝ y) ≡ y
  -- TODO: Follows from quotient structure once δ and choose-k are proper
  fromℝ-toℝ : (x : ℝsd) → fromℝ (toℝ x) ≡ x

------------------------------------------------------------------------
-- Type equivalence
------------------------------------------------------------------------

ℝsd≃ℝ : ℝsd ≃ ℝ
ℝsd≃ℝ = isoToEquiv (iso toℝ fromℝ toℝ-fromℝ fromℝ-toℝ)

ℝsd≡ℝ : ℝsd ≡ ℝ
ℝsd≡ℝ = ua ℝsd≃ℝ
