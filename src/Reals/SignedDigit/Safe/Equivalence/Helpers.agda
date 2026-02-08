{-# OPTIONS --cubical --safe --guardedness #-}

module Reals.SignedDigit.Safe.Equivalence.Helpers where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Int as ℤ using (ℤ ; pos)
open import Cubical.Data.Sigma using (Σ ; _,_ ; fst ; _×_)

open import Cubical.HITs.CauchyReals.Base using (ℝ)
open import Reals.SignedDigit.Safe.Bounded using (ℝ[-1,1] ; clamp-to-𝕀sd)

ℝ∈OpenUnit : Type₀
ℝ∈OpenUnit = ℝ[-1,1]

val : ℝ∈OpenUnit → ℝ
val = fst

choose-k : ℝ → ℤ × ℝ∈OpenUnit
choose-k x = pos 0 , clamp-to-𝕀sd x
