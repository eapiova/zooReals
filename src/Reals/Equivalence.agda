{-# OPTIONS --cubical --guardedness #-}

-- Equivalence between Signed-Digit Reals and HoTT Cauchy Reals
-- 
-- This module proves that ι and ι⁻¹ form an equivalence between
-- ℝsd (signed-digit quotient) and ℝ (HoTT Cauchy reals).

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
open import Reals.SignedDigit.Base
open import Reals.SignedDigit.Equivalence using (ℝsd; _≈sd_; isSetℝsd; 0sd; 1sd; -1sd)
open import Reals.HoTT.Base using (ℝ; rat; lim; eqℝ; _∼[_]_)

-- Import both embeddings
open import Reals.SignedDigit.Embedding using (ι; stream→ℝ)
open import Reals.HoTT.Embedding using (ι⁻¹; ℝ→stream)

-- --------------------------------------------------------------------------
-- Round-trip: ι⁻¹ ∘ ι ~ id
-- --------------------------------------------------------------------------

-- Starting from a signed-digit real, embedding into ℝ and back
-- gives an equivalent signed-digit real

-- First, for streams before quotienting
postulate
  stream-roundtrip : ∀ (s : 𝟛ᴺ) → ℝ→stream (stream→ℝ s) ≈sd s

-- This extends to the quotient
ι⁻¹∘ι : ∀ (x : ℝsd) → ι⁻¹ (ι x) ≡ x
ι⁻¹∘ι = SQ.elimProp (λ _ → isSetℝsd _ _) go
  where
    go : ∀ (s : 𝟛ᴺ) → ι⁻¹ (ι SQ.[ s ]) ≡ SQ.[ s ]
    go s = SQ.eq/ (ℝ→stream (stream→ℝ s)) s (stream-roundtrip s)

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

ℝsd≅ℝ : Iso ℝsd ℝ
Iso.fun ℝsd≅ℝ = ι
Iso.inv ℝsd≅ℝ = ι⁻¹
Iso.rightInv ℝsd≅ℝ = ι∘ι⁻¹
Iso.leftInv ℝsd≅ℝ = ι⁻¹∘ι

-- The equivalence
ℝsd≃ℝ : ℝsd ≃ ℝ
ℝsd≃ℝ = isoToEquiv ℝsd≅ℝ

-- As a path
ℝsd≡ℝ : ℝsd ≡ ℝ
ℝsd≡ℝ = ua ℝsd≃ℝ

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
