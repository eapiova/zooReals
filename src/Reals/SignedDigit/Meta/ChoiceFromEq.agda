{-# OPTIONS --cubical --guardedness #-}

module Reals.SignedDigit.Meta.ChoiceFromEq where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma using (Σ; Σ-syntax; _,_; fst; snd)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Rationals.Fast.Order using (ℚ₊)

open import Cubical.HITs.CauchyReals.Base using (ℝ)
open import Reals.SignedDigit.Representation using (ℝsd; toℝ)
open import Reals.SignedDigit.Meta.AssumeEq using ()

module _ (H : ℝsd ≃ ℝ) (H-fun≡toℝ : equivFun H ≡ toℝ) where

  private
    sectionℝ : ℝ → ℝsd
    sectionℝ =
      Reals.SignedDigit.Meta.AssumeEq.sectionℝ H H-fun≡toℝ

    sectionβ : (x : ℝ) → toℝ (sectionℝ x) ≡ x
    sectionβ =
      Reals.SignedDigit.Meta.AssumeEq.sectionβ H H-fun≡toℝ

  familySection : (I : Type₀) → (f : I → ℝ) →
    Σ[ g ∈ (I → ℝsd) ] ((i : I) → toℝ (g i) ≡ f i)
  familySection I f = g , gβ
    where
      g : I → ℝsd
      g i = sectionℝ (f i)

      gβ : (i : I) → toℝ (g i) ≡ f i
      gβ i = sectionβ (f i)

  familySection-ℚ₊ : (f : ℚ₊ → ℝ) →
    Σ[ g ∈ (ℚ₊ → ℝsd) ] ((ε : ℚ₊) → toℝ (g ε) ≡ f ε)
  familySection-ℚ₊ = familySection ℚ₊

  constantSection : (x : ℝ) → Σ[ y ∈ ℝsd ] toℝ y ≡ x
  constantSection x = fst pair tt , snd pair tt
    where
      pair : Σ[ g ∈ (Unit → ℝsd) ] ((u : Unit) → toℝ (g u) ≡ x)
      pair = familySection Unit (λ _ → x)
