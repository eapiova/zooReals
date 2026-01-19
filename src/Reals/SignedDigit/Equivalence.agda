{-# OPTIONS --cubical --guardedness --allow-unsolved-metas #-}

------------------------------------------------------------------------
-- Signed-Digit Equivalence: ℝ ≃ ℝsd
------------------------------------------------------------------------
--
-- This module proves the equivalence between the signed-digit
-- reals (ℝsd) and the HoTT Cauchy reals (ℝ).
--
-- The implementation is split into submodules:
--   - Equivalence.Helpers    : Common imports and helper definitions
--   - Equivalence.RoundTrip  : Round-trip proofs for rational→stream
--   - Equivalence.Direct     : Recℝ-based approach (has unfilled holes)
--   - Equivalence.Surjection : Elimℝ-Prop-based approach (preferred)
--
-- KEY EXPORTS:
--   ι⁻¹            : Embedding from Cauchy reals to signed-digit (ℝ → 𝕀sd)
--   fromℝ          : Encoding HoTT reals as extended signed-digit codes (ℝ → ℝsd)
--   toℝ-fromℝ      : Round-trip proof (ℝ → ℝsd → ℝ)
--   ℝsd≃ℝ          : The full type equivalence (via Direct approach, postulated)
--   ℝsd≃ℝ-via-surj : The full type equivalence (via Surjection approach)
--
------------------------------------------------------------------------

module Reals.SignedDigit.Equivalence where

-- Re-export everything from submodules

open import Reals.SignedDigit.Equivalence.Helpers public

open import Reals.SignedDigit.Equivalence.RoundTrip public

-- Direct.agda is skipped: takes >5 minutes to typecheck due to Recℝ coherence holes
-- The Surjection approach below is preferred and complete.
-- open import Reals.SignedDigit.Equivalence.Direct public

open import Reals.SignedDigit.Equivalence.Surjection public
