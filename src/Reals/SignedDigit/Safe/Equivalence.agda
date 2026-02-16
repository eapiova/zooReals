{-# OPTIONS --cubical --guardedness #-}

module Reals.SignedDigit.Safe.Equivalence where

open import Reals.SignedDigit.Safe.Bounded public using (ℝ[-1,1])
-- Full safe ℝsd exports are intentionally absent until a genuine
-- quotient-based safe representation is introduced.
open import Reals.SignedDigit.Safe.Equivalence.Direct public
  using ( ι⁻¹
        ; ℝ→𝕀sd-direct
        )
