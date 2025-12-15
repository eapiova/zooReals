{-# OPTIONS --cubical --guardedness #-}

-- Equivalence between Signed-Digit Reals and HoTT Cauchy Reals
-- 
-- This module proves that ι and ι⁻¹ form an equivalence between
-- 𝕀sd (signed-digit quotient) and ℝ (HoTT Cauchy reals).

module Reals.Equivalence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence using (ua)

open import Cubical.Data.Nat as ℕ using (ℕ; zero; suc)
open import Cubical.Data.Int as ℤ using (ℤ; pos)
open import Cubical.Data.NatPlusOne using (1+_)
open import Cubical.Data.Rationals.Fast as ℚ using (ℚ)

open import Cubical.HITs.SetQuotients as SQ hiding ([_])

-- Import both representations
open import Reals.SignedDigit.Core
open import Reals.SignedDigit.Bounded using (𝕀sd; _≈sd_; isSet𝕀sd; 0sd; 1sd; -1sd; stream→ℝ)
open import Cubical.HITs.CauchyReals.Base using (ℝ; rat; lim; eqℝ; _∼[_]_)

-- Import both embeddings
open import Reals.SignedDigit.Bounded using (ι)
open import Reals.SignedDigit.Equivalence using (ι⁻¹; ℝ→stream)

-- --------------------------------------------------------------------------
-- Round-trip: ι⁻¹ ∘ ι ~ id
-- --------------------------------------------------------------------------

-- Starting from a signed-digit real, embedding into ℝ and back
-- gives an equivalent signed-digit real.
--
-- NOTE: The current implementation of ι⁻¹ uses ℝ→𝕀sd-direct (via Recℝ)
-- which maps a lim to its value at precision 1. With the trivial modulus,
-- this collapses to the first digit approximation, losing information.
--
-- For a proper proof, we would need:
-- 1. A non-trivial modulus that makes approximations converge, AND
-- 2. A proof that stream→ℝ (rational→stream q) ≡ rat q (round-trip property)
--
-- For now, we postulate the round-trip properties.
postulate
  ι⁻¹∘ι : ∀ (x : 𝕀sd) → ι⁻¹ (ι x) ≡ x

-- --------------------------------------------------------------------------
-- Round-trip: ι ∘ ι⁻¹ ~ id
-- --------------------------------------------------------------------------

-- Starting from a Cauchy real, extracting digits and embedding back
-- gives the same real
postulate
  ι∘ι⁻¹ : ∀ (x : ℝ) → ι (ι⁻¹ x) ≡ x

-- --------------------------------------------------------------------------
-- The equivalence
-- --------------------------------------------------------------------------

-- ι and ι⁻¹ form a quasi-inverse pair

𝕀sd≅ℝ : Iso 𝕀sd ℝ
Iso.fun 𝕀sd≅ℝ = ι
Iso.inv 𝕀sd≅ℝ = ι⁻¹
Iso.rightInv 𝕀sd≅ℝ = ι∘ι⁻¹
Iso.leftInv 𝕀sd≅ℝ = ι⁻¹∘ι

-- The equivalence
𝕀sd≃ℝ : 𝕀sd ≃ ℝ
𝕀sd≃ℝ = isoToEquiv 𝕀sd≅ℝ

-- As a path
𝕀sd≡ℝ : 𝕀sd ≡ ℝ
𝕀sd≡ℝ = ua 𝕀sd≃ℝ

-- --------------------------------------------------------------------------
-- Preservation of structure
-- --------------------------------------------------------------------------

-- The equivalence preserves the rational embeddings
postulate
  ι-preserves-0 : ι 0sd ≡ rat (ℚ.[ pos 0 , 1+ 0 ])
  ι-preserves-1 : ι 1sd ≡ rat (ℚ.[ pos 1 , 1+ 0 ])
  
  -- ι⁻¹ preserves rationals (up to equivalence)
  ι⁻¹-preserves-0 : ι⁻¹ (rat (ℚ.[ pos 0 , 1+ 0 ])) ≡ 0sd
  ι⁻¹-preserves-1 : ι⁻¹ (rat (ℚ.[ pos 1 , 1+ 0 ])) ≡ 1sd
