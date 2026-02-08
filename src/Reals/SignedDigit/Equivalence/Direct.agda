{-# OPTIONS --cubical --guardedness #-}

------------------------------------------------------------------------
-- Signed-Digit Equivalence: Direct Approach via Recℝ
------------------------------------------------------------------------
--
-- This module re-exports the signed-digit equivalence components:
--   - Direct.Rec:  ι⁻¹, ℝ→𝕀sd-direct (heavy Recℝ, compiles once)
--   - Direct.Full: fromℝ, ℝsd≃ℝ (heavy Order/Multiplication imports)
--
-- Import this module for the full API. Import Direct.Rec directly
-- if you only need ι⁻¹ and want fast compilation.
--
------------------------------------------------------------------------

module Reals.SignedDigit.Equivalence.Direct where

-- Core embedding (fast to load from cached .agdai)
open import Reals.SignedDigit.Equivalence.Direct.Rec public
  using (ι⁻¹; ℝ→𝕀sd-direct)

-- Full equivalence (heavy imports: Order, Multiplication)
open import Reals.SignedDigit.Equivalence.Direct.Full public
  using (fromℝ; ℝsd≃ℝ; ℝsd≡ℝ; toℝ-fromℝ; fromℝ-toℝ; lift-to-ℝsd)
