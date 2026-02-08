{-# OPTIONS --cubical --safe --guardedness #-}

------------------------------------------------------------------------
-- Coherence Base: Shared Types and Helpers
------------------------------------------------------------------------
--
-- This module contains shared definitions for the coherence proofs:
-- - 𝕀sd-B type alias
-- - ratA helper
-- - Abstract arithmetic helpers
--
------------------------------------------------------------------------

module Reals.SignedDigit.Safe.Equivalence.Coherence.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Int as ℤ using (ℤ; pos)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.HITs.SetQuotients as SQ hiding ([_])
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Data.Rationals.Fast as ℚ
open import Cubical.Data.Rationals.Fast.Properties as ℚP
open import Cubical.Data.Rationals.Fast.Order as ℚO
  using (ℚ₊; minus-<; isTrans<≤; isTrans<; ℚ₊≡; 0<ℚ₊)
open import Cubical.Data.Rationals.Fast.Order.Properties as ℚOP
  using (/2₊)

open import Cubical.HITs.CauchyReals.Base as ℝBase using (ℝ; rat; _∼[_]_; rat-rat-fromAbs)
open import Cubical.HITs.CauchyReals.Closeness using (triangle∼; sym∼)

open import Reals.SignedDigit.Safe.Core
open import Reals.SignedDigit.Safe.Bounded using (𝕀sd; isSet𝕀sd; stream→ℝ; rational→stream; clampℚ; clamp-lip; ι; 0ℚ)
open import Reals.SignedDigit.Safe.Equivalence.Arithmetic
  using (_+₊_)

------------------------------------------------------------------------
-- The B relation for Recℝ
------------------------------------------------------------------------

-- We use 2ε-closeness in ℝ via the embedding ι.
𝕀sd-B : 𝕀sd → 𝕀sd → ℚ₊ → Type₀
𝕀sd-B a a' ε = ι a ∼[ ε +₊ ε ] ι a'

------------------------------------------------------------------------
-- ratA helper
------------------------------------------------------------------------

ratA : ℚ.ℚ → 𝕀sd
ratA q = SQ.[ rational→stream q ]

------------------------------------------------------------------------
-- Abstract helpers to prevent term explosion
------------------------------------------------------------------------

abstract
  neg-flip : (a e : ℚ.ℚ) → (ℚP.- e) ℚO.< a → (ℚP.- a) ℚO.< e
  neg-flip a e proof = subst ((ℚP.- a) ℚO.<_) (ℚP.-Invol e) (minus-< (ℚP.- e) a proof)

  max<→ : (a b c : ℚ.ℚ) → a ℚO.< c → b ℚO.< c → ℚP.max a b ℚO.< c
  max<→ a b c a<c b<c = PT.rec (ℚO.isProp< (ℚP.max a b) c) handle (ℚO.isTotal≤ a b)
    where
      handle : (a ℚO.≤ b) ⊎ (b ℚO.≤ a) → ℚP.max a b ℚO.< c
      handle (inl a≤b) = subst (ℚO._< c) (sym (ℚO.≤→max a b a≤b)) b<c
      handle (inr b≤a) = subst (ℚO._< c) (sym (ℚP.maxComm a b ∙ ℚO.≤→max b a b≤a)) a<c

  ε<2ε : (ε : ℚ₊) → fst ε ℚO.< fst (ε +₊ ε)
  ε<2ε ε = subst (ℚO._< (fst ε ℚ.+ fst ε)) (ℚP.+IdR (fst ε))
                 (ℚO.<-o+ 0ℚ (fst ε) (fst ε) (0<ℚ₊ ε))
