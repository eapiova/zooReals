{-# OPTIONS --cubical --guardedness #-}

------------------------------------------------------------------------
-- Signed-digit stream averaging (placeholder interface)
------------------------------------------------------------------------
--
-- This module isolates the algorithmic average operation used by the
-- midpoint structure on 𝕀sd.
--
-- Milestone-2 target:
--   replace these postulates with a constructive stream algorithm and
--   a proof of semantic correctness.

module Reals.SignedDigit.Midpoint.Average where

open import Cubical.Foundations.Prelude

open import Cubical.HITs.CauchyReals.Order using (_+ᵣ_)
open import Cubical.HITs.CauchyReals.Multiplication using (/2ᵣ)

open import Reals.SignedDigit.Core using (𝟛ᴺ)
open import Reals.SignedDigit.Bounded using (stream→ℝ)

postulate
  avg : 𝟛ᴺ → 𝟛ᴺ → 𝟛ᴺ
  avg-sem : ∀ s t → stream→ℝ (avg s t) ≡ /2ᵣ (stream→ℝ s +ᵣ stream→ℝ t)
