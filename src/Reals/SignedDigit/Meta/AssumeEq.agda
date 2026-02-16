{-# OPTIONS --cubical --guardedness #-}

module Reals.SignedDigit.Meta.AssumeEq where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.HITs.CauchyReals.Base using (ℝ)
open import Reals.SignedDigit.Representation using (ℝsd; toℝ)

-- Work under:
--   1) an equivalence witness H : ℝsd ≃ ℝ, and
--   2) identification of its forward map with the repository map toℝ.
module _ (H : ℝsd ≃ ℝ) (H-fun≡toℝ : equivFun H ≡ toℝ) where

  sectionℝ : ℝ → ℝsd
  sectionℝ = invEq H

  sectionβ : (x : ℝ) → toℝ (sectionℝ x) ≡ x
  sectionβ x =
    subst (λ f → f (sectionℝ x) ≡ x) H-fun≡toℝ (secEq H x)

  sectionη : (x : ℝsd) → sectionℝ (toℝ x) ≡ x
  sectionη x =
    subst (λ f → sectionℝ (f x) ≡ x) H-fun≡toℝ (retEq H x)
