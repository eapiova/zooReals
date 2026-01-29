{-# OPTIONS --cubical --guardedness #-}

------------------------------------------------------------------------
-- Coherence: rat-rat-B proof
------------------------------------------------------------------------

module Reals.SignedDigit.Equivalence.Coherence.RatRat where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals.Fast as ℚ
open import Cubical.Data.Rationals.Fast.Properties as ℚP
open import Cubical.Data.Rationals.Fast.Order as ℚO
  using (ℚ₊; isTrans<; isTrans≤<)

open import Cubical.HITs.CauchyReals.Base using (rat-rat-fromAbs; _∼[_]_)

open import Reals.SignedDigit.Bounded using (clampℚ; clamp-lip)
open import Reals.SignedDigit.Equivalence.RoundTrip using (round-trip-clamped)
open import Reals.SignedDigit.Equivalence.Arithmetic using (_+₊_)
open import Reals.SignedDigit.Equivalence.Coherence.Base

------------------------------------------------------------------------
-- rat-rat-B proof
------------------------------------------------------------------------

abstract
  rat-rat-B-proof : (q r : ℚ.ℚ) (ε : ℚ₊) →
                    (ℚP.- fst ε) ℚO.< (q ℚP.- r) →
                    (q ℚP.- r) ℚO.< fst ε →
                    𝕀sd-B (ratA q) (ratA r) ε
  rat-rat-B-proof q r ε vₗ vᵤ =
    subst2 (λ a b → a ∼[ ε +₊ ε ] b) (sym (round-trip-clamped q)) (sym (round-trip-clamped r))
           (rat-rat-fromAbs (clampℚ q) (clampℚ r) (ε +₊ ε) clamped-bound-2ε)
    where
      x : ℚ.ℚ
      x = q ℚP.- r
      ε' : ℚ.ℚ
      ε' = fst ε

      neg-x<ε : (ℚP.- x) ℚO.< ε'
      neg-x<ε = neg-flip x ε' vₗ

      abs-bound : ℚP.abs x ℚO.< ε'
      abs-bound = max<→ x (ℚP.- x) ε' vᵤ neg-x<ε

      clamped-bound : ℚP.abs (clampℚ q ℚP.- clampℚ r) ℚO.< ε'
      clamped-bound = ℚO.isTrans≤< _ _ _ (clamp-lip q r) abs-bound

      clamped-bound-2ε : ℚP.abs (clampℚ q ℚP.- clampℚ r) ℚO.< fst (ε +₊ ε)
      clamped-bound-2ε = ℚO.isTrans< _ _ _ clamped-bound (ε<2ε ε)
