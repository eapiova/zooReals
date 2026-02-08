{-# OPTIONS --cubical --safe --guardedness #-}

------------------------------------------------------------------------
-- Recℝ Instantiation for ℝ → 𝕀sd
------------------------------------------------------------------------
--
-- This module contains the heavy Recℝ record instantiation and the
-- resulting ℝ→𝕀sd-direct function. It is separated from Direct.agda
-- so that the expensive elaboration (20+ min, 27GB) only happens once
-- and gets cached as an .agdai interface file.
--
-- KEY EXPORTS:
--   ι⁻¹            : ℝ → 𝕀sd
--   ℝ→𝕀sd-direct   : ℝ → 𝕀sd (same as ι⁻¹)
--
------------------------------------------------------------------------

module Reals.SignedDigit.Safe.Equivalence.Direct.Rec where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (isPropΠ)

open import Cubical.HITs.SetQuotients as SQ hiding ([_])

open import Cubical.Data.Rationals.Fast.Order as ℚO
  using (ℚ₊)
open import Cubical.Data.Rationals.Fast.Order.Properties as ℚOP
  using (/2₊; ε/2+ε/2≡ε)

open import Cubical.HITs.CauchyReals.Base as ℝBase using (ℝ; rat; eqℝ; _∼[_]_; Recℝ; isProp∼)

open import Reals.SignedDigit.Safe.Bounded using (𝕀sd; isSet𝕀sd; rational→stream; ι)
open import Reals.SignedDigit.Safe.Limit using (limA-𝕀sd; limA-𝕀sd-close)
open import Reals.SignedDigit.Safe.Equivalence.Arithmetic
  using (_+₊_; /2₊+/2₊≡ε₊)
open import Reals.SignedDigit.Safe.Equivalence.Coherence
  using (𝕀sd-B; rat-rat-B-proof; rat-lim-B-proof; lim-rat-B-proof; lim-lim-B-proof)

------------------------------------------------------------------------
-- ι-inj: quotient injectivity
------------------------------------------------------------------------

ι-inj : ∀ a a' → ι a ≡ ι a' → a ≡ a'
ι-inj = SQ.elimProp2
          (λ a a' → isPropΠ (λ _ → isSet𝕀sd a a'))
          (λ s t h → eq/ s t h)

-- Convert coherence from modified B (∼[2ε]) to standard (∼[ε])
B→std-close : (a a' : 𝕀sd) → (∀ ε → 𝕀sd-B a a' ε) → (∀ ε → ι a ∼[ ε ] ι a')
B→std-close a a' allClose ε = subst (λ x → ι a ∼[ x ] ι a') (/2₊+/2₊≡ε₊ ε) (allClose (/2₊ ε))

------------------------------------------------------------------------
-- Building the Recℝ structure for ℝ → 𝕀sd
------------------------------------------------------------------------

abstract
  ℝ→𝕀sd-Rec : Recℝ 𝕀sd 𝕀sd-B
  Recℝ.ratA ℝ→𝕀sd-Rec q = SQ.[ rational→stream q ]

  Recℝ.limA ℝ→𝕀sd-Rec streams coherence = limA-𝕀sd streams coherence

  Recℝ.eqA ℝ→𝕀sd-Rec a a' allClose = ι-inj a a' (eqℝ (ι a) (ι a') (B→std-close a a' allClose))

  Recℝ.rat-rat-B ℝ→𝕀sd-Rec = rat-rat-B-proof
  Recℝ.rat-lim-B ℝ→𝕀sd-Rec = rat-lim-B-proof
  Recℝ.lim-rat-B ℝ→𝕀sd-Rec = lim-rat-B-proof
  Recℝ.lim-lim-B ℝ→𝕀sd-Rec = lim-lim-B-proof

  Recℝ.isPropB ℝ→𝕀sd-Rec a a' ε = isProp∼ (ι a) (ε +₊ ε) (ι a')

  ℝ→𝕀sd-direct : ℝ → 𝕀sd
  ℝ→𝕀sd-direct = Recℝ.go ℝ→𝕀sd-Rec

------------------------------------------------------------------------
-- The main embedding function
------------------------------------------------------------------------

ι⁻¹ : ℝ → 𝕀sd
ι⁻¹ = ℝ→𝕀sd-direct
