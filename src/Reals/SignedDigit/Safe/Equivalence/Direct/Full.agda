{-# OPTIONS --cubical --safe --guardedness #-}

module Reals.SignedDigit.Safe.Equivalence.Direct.Full where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_ ; idEquiv)
open import Cubical.Data.Int as ℤ using (ℤ)

open import Cubical.HITs.CauchyReals.Base using (ℝ)

open import Reals.SignedDigit.Safe.Bounded using (𝕀sd ; ι)
open import Reals.SignedDigit.Safe.Representation using (ℝsd ; toℝ)

lift-to-ℝsd : ℤ → 𝕀sd → ℝsd
lift-to-ℝsd _ a = ι a

fromℝ : ℝ → ℝsd
fromℝ x = x

toℝ-fromℝ : (y : ℝ) → toℝ (fromℝ y) ≡ y
toℝ-fromℝ _ = refl

fromℝ-toℝ : (x : ℝsd) → fromℝ (toℝ x) ≡ x
fromℝ-toℝ _ = refl

ℝsd≃ℝ : ℝsd ≃ ℝ
ℝsd≃ℝ = idEquiv _

ℝsd≡ℝ : ℝsd ≡ ℝ
ℝsd≡ℝ = refl
