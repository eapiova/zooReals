{-# OPTIONS --cubical --safe --guardedness #-}

module Reals.SignedDigit.Safe.Equivalence where

open import Reals.SignedDigit.Safe.Bounded public using (ℝ[-1,1])
open import Reals.SignedDigit.Safe.Equivalence.Direct public
  using ( ι⁻¹
        ; 𝕀sd≃ℝ[-1,1]
        ; fromℝ
        ; toℝ-fromℝ
        ; ℝsd≃ℝ
        ; ℝsd≡ℝ
        )
