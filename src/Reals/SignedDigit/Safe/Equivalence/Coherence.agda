{-# OPTIONS --cubical --guardedness #-}

------------------------------------------------------------------------
-- Coherence Proofs for Signed-Digit Equivalence
------------------------------------------------------------------------
--
-- This module re-exports the coherence proofs from submodules.
-- Each proof is in a separate file for faster incremental compilation.
--
------------------------------------------------------------------------

module Reals.SignedDigit.Safe.Equivalence.Coherence where

-- Re-export the B relation type and ratA helper
open import Reals.SignedDigit.Safe.Equivalence.Coherence.Base public
  using (𝕀sd-B; ratA)

-- Re-export the four coherence proofs
open import Reals.SignedDigit.Safe.Equivalence.Coherence.RatRat public
  using (rat-rat-B-proof)

open import Reals.SignedDigit.Safe.Equivalence.Coherence.RatLim public
  using (rat-lim-B-proof)

open import Reals.SignedDigit.Safe.Equivalence.Coherence.LimRat public
  using (lim-rat-B-proof)

open import Reals.SignedDigit.Safe.Equivalence.Coherence.LimLim public
  using (lim-lim-B-proof)
