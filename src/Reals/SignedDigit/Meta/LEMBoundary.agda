{-# OPTIONS --cubical --guardedness #-}

module Reals.SignedDigit.Meta.LEMBoundary where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Relation.Nullary using (Dec; yes; no; ¬_)

open import Cubical.HITs.CauchyReals.Base using (ℝ)
open import Reals.SignedDigit.Representation using (ℝsd; toℝ)
open import Reals.SignedDigit.Meta.AssumeEq using ()

LEM : Type₁
LEM = (P : Type₀) → isProp P → P ⊎ (¬ P)

record PropReflectionIntoℝ : Type₁ where
  field
    Decoded : ℝsd → Type₀
    Decoded-dec : (x : ℝsd) → Dec (Decoded x)

    encodeProp : (P : Type₀) → isProp P → ℝ

    decode-to-prop :
      (H : ℝsd ≃ ℝ) →
      (H-fun≡toℝ : equivFun H ≡ toℝ) →
      (P : Type₀) →
      (isP : isProp P) →
      Decoded (Reals.SignedDigit.Meta.AssumeEq.sectionℝ H H-fun≡toℝ (encodeProp P isP)) →
      P

    prop-to-decode :
      (H : ℝsd ≃ ℝ) →
      (H-fun≡toℝ : equivFun H ≡ toℝ) →
      (P : Type₀) →
      (isP : isProp P) →
      P →
      Decoded (Reals.SignedDigit.Meta.AssumeEq.sectionℝ H H-fun≡toℝ (encodeProp P isP))

lem-from-eq-and-reflection :
  (H : ℝsd ≃ ℝ) →
  (H-fun≡toℝ : equivFun H ≡ toℝ) →
  PropReflectionIntoℝ →
  LEM
lem-from-eq-and-reflection H H-fun≡toℝ R P isP =
  decide (PropReflectionIntoℝ.Decoded-dec R code)
  where
    sectionℝ : ℝ → ℝsd
    sectionℝ =
      Reals.SignedDigit.Meta.AssumeEq.sectionℝ H H-fun≡toℝ

    code : ℝsd
    code = sectionℝ (PropReflectionIntoℝ.encodeProp R P isP)

    decide : Dec (PropReflectionIntoℝ.Decoded R code) → P ⊎ (¬ P)
    decide (yes d) =
      inl (PropReflectionIntoℝ.decode-to-prop R H H-fun≡toℝ P isP d)
    decide (no ¬d) =
      inr (λ p → ¬d (PropReflectionIntoℝ.prop-to-decode R H H-fun≡toℝ P isP p))
