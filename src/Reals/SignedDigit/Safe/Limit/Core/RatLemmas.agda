{-# OPTIONS --cubical --safe --guardedness #-}

module Reals.SignedDigit.Safe.Limit.Core.RatLemmas where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Rationals.Fast as ℚ
open import Cubical.Data.Rationals.Fast.Properties as ℚP
open import Cubical.Data.Rationals.Fast.Order as ℚO using (ℚ₊; ℚ₊≡)
open import Cubical.Data.Rationals.Fast.Order.Properties as ℚOP using (/2₊; /4₊)
open import Cubical.Tactics.CommRingSolverFast.FastRationalsReflection using (ℚ!!)

-- Division helper: ε/8 = (ε/2)/4
/8₊ : ℚ₊ → ℚ₊
/8₊ ε = /4₊ (/2₊ ε)

abstract
  -- /2₊ (/4₊ ε) ≡ /8₊ ε (commutativity of halving and quartering)
  /2₊∘/4₊≡/8₊ : ∀ ε → /2₊ (/4₊ ε) ≡ /8₊ ε
  /2₊∘/4₊≡/8₊ ε = ℚ₊≡ ℚ!!

  -- Distributivity: c · a - c · b = c · (a - b)
  ·DistL- : (c a b : ℚ.ℚ) → (c ℚP.· a) ℚP.- (c ℚP.· b) ≡ c ℚP.· (a ℚP.- b)
  ·DistL- c a b = ℚ!!

  -- Ring identity: (a - c) - (b - c) = a - b
  sub-cancel : (a b c : ℚ.ℚ) → (a ℚP.- c) ℚP.- (b ℚP.- c) ≡ a ℚP.- b
  sub-cancel a b c = ℚ!!

  -- Ring identity: (a + b) - (a + c) = b - c
  plus-cancel-same : (a b c : ℚ.ℚ) → (a ℚP.+ b) ℚP.- (a ℚP.+ c) ≡ b ℚP.- c
  plus-cancel-same a b c = ℚ!!
