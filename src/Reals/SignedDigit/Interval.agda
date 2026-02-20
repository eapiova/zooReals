{-# OPTIONS --cubical --guardedness #-}

------------------------------------------------------------------------
-- Shared bounded interval interface for signed-digit quotient semantics
------------------------------------------------------------------------
--
-- This module centralizes the bounded codomain used by:
--   - HCIT terminality (semantics land in [-1,1])
--   - midpoint real structure (ι lifts to the bounded subtype)
--
-- POSTULATE:
--   ι-bounded : image of ι lies in [-1,1]
-- This is semantic arithmetic, not AC_ω.

module Reals.SignedDigit.Interval where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (isSetΣ; isProp×)

open import Cubical.Data.Sigma

open import Cubical.HITs.CauchyReals.Base using (ℝ; rat)
open import Cubical.HITs.CauchyReals.Closeness using (isSetℝ)
open import Cubical.HITs.CauchyReals.Order using (_≤ᵣ_; isProp≤ᵣ)

open import Reals.SignedDigit.Core using (-1d; +1d)
open import Reals.SignedDigit.Bounded
  using (𝕀sd; ι; digitToℚ)

-1ℝ : ℝ
-1ℝ = rat (digitToℚ -1d)

+1ℝ : ℝ
+1ℝ = rat (digitToℚ +1d)

ℝ[-1,1] : Type₀
ℝ[-1,1] = Σ ℝ (λ x → (-1ℝ ≤ᵣ x) × (x ≤ᵣ +1ℝ))

isSetℝ[-1,1] : isSet ℝ[-1,1]
isSetℝ[-1,1] = isSetΣ isSetℝ
  (λ _ → isProp→isSet (isProp× (isProp≤ᵣ _ _) (isProp≤ᵣ _ _)))

-- Equality in ℝ[-1,1] reduces to equality of underlying ℝ values.
ℝ[-1,1]-≡ : {a b : ℝ[-1,1]} → fst a ≡ fst b → a ≡ b
ℝ[-1,1]-≡ = Σ≡Prop (λ _ → isProp× (isProp≤ᵣ _ _) (isProp≤ᵣ _ _))

postulate
  ι-bounded : ∀ (x : 𝕀sd) → (-1ℝ ≤ᵣ ι x) × (ι x ≤ᵣ +1ℝ)

-- Canonical lift of ι into the bounded subtype.
ι↑ : 𝕀sd → ℝ[-1,1]
ι↑ x = ι x , ι-bounded x
