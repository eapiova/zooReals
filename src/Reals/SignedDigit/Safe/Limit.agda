{-# OPTIONS --cubical --guardedness #-}

------------------------------------------------------------------------
-- Safe Limit Operations + Quotient Lift Postulates
------------------------------------------------------------------------
--
-- Re-exports the safe raw-stream limit operations from Core,
-- and postulates the quotient lift `limA-𝕀sd` which requires
-- countable dependent choice (AC_ω) — not provable in --safe
-- Cubical Agda. See the plan file for the full analysis.
--

module Reals.SignedDigit.Safe.Limit where

open import Cubical.Data.Rationals.Fast.Order as ℚO using (ℚ₊)
open import Cubical.HITs.CauchyReals.Base using (_∼[_]_)

open import Reals.SignedDigit.Safe.Bounded using (𝕀sd; ι)
open import Reals.SignedDigit.Safe.Equivalence.Arithmetic using (_+₊_)

-- Re-export all safe raw-stream operations (limA, limA-eq, etc.)
open import Reals.SignedDigit.Safe.Limit.Core public

------------------------------------------------------------------------
-- Quotient lift postulates
------------------------------------------------------------------------
--
-- limA-𝕀sd cannot be proven without AC_ω (countable dependent choice).
-- The obstruction: given f : ℚ₊ → 𝕀sd (where 𝕀sd = 𝟛ᴺ / ≈sd),
-- we need representatives h : ℚ₊ → 𝟛ᴺ to feed to limA. Extracting h
-- from f requires ∀ δ → ∥ fiber [_] (f δ) ∥₁ → ∥ ∀ δ → fiber [_] (f δ) ∥₁
-- which is AC_ω. Six approaches were investigated; all fail.
--
-- The postulates are consistent with univalence and used in constructive
-- mathematics. The proof sketch is in Limit.agda:665-682.

postulate
  limA-𝕀sd : (f : ℚ₊ → 𝕀sd) →
             (coh : ∀ δ ε → ι (f δ) ∼[ (δ +₊ ε) +₊ (δ +₊ ε) ] ι (f ε)) →
             𝕀sd

  limA-𝕀sd-close : (f : ℚ₊ → 𝕀sd) →
                   (coh : ∀ δ ε → ι (f δ) ∼[ (δ +₊ ε) +₊ (δ +₊ ε) ] ι (f ε)) →
                   ∀ δ → ι (limA-𝕀sd f coh) ∼[ δ +₊ δ ] ι (f δ)
