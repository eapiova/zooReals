{-# OPTIONS --cubical --safe --guardedness #-}

------------------------------------------------------------------------
-- Signed-Digit Primitives and Streams
------------------------------------------------------------------------
--
-- This module defines the foundational types for signed-digit arithmetic:
-- 1. Digits {-1, 0, +1}
-- 2. Streams of digits (𝟛ᴺ)
--
-- Based on TWA Thesis Chapter 5 (TypeTopology).
------------------------------------------------------------------------

module Reals.SignedDigit.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat as ℕ using (ℕ; zero; suc)
open import Cubical.Data.Int as ℤ using (ℤ; pos; negsuc)
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥

-- Use Stream from Cubical library
open import Cubical.Codata.Stream as StreamM using (Stream; _,_; mapS)
open import Cubical.Codata.Stream.Properties using (module Stream≅Nat→)
open StreamM.Stream public

------------------------------------------------------------------------
-- Ternary signed digits: {-1, 0, +1}
------------------------------------------------------------------------

data Digit : Type₀ where
  -1d : Digit
  0d  : Digit
  +1d : Digit

-- Digit is discrete (decidable equality)
open import Cubical.Relation.Nullary

discreteDigit : Discrete Digit
discreteDigit -1d -1d = yes refl
discreteDigit -1d 0d  = no (λ p → subst (λ { -1d → Digit ; 0d → ⊥ ; +1d → ⊥ }) p -1d)
discreteDigit -1d +1d = no (λ p → subst (λ { -1d → Digit ; 0d → ⊥ ; +1d → ⊥ }) p -1d)
discreteDigit 0d -1d  = no (λ p → subst (λ { -1d → ⊥ ; 0d → Digit ; +1d → ⊥ }) p 0d)
discreteDigit 0d 0d   = yes refl
discreteDigit 0d +1d  = no (λ p → subst (λ { -1d → ⊥ ; 0d → Digit ; +1d → ⊥ }) p 0d)
discreteDigit +1d -1d = no (λ p → subst (λ { -1d → ⊥ ; 0d → ⊥ ; +1d → Digit }) p +1d)
discreteDigit +1d 0d  = no (λ p → subst (λ { -1d → ⊥ ; 0d → ⊥ ; +1d → Digit }) p +1d)
discreteDigit +1d +1d = yes refl

-- Digit is a set (discrete types are sets)
isSetDigit : isSet Digit
isSetDigit = Discrete→isSet discreteDigit


------------------------------------------------------------------------
-- Signed-digit sequences using Cubical Stream
------------------------------------------------------------------------

-- Type of signed-digit sequences (infinite streams of digits)
-- Each stream α represents: Σᵢ αᵢ / 2^(i+1) ∈ [-1, 1]
𝟛ᴺ : Type₀
𝟛ᴺ = Stream Digit

-- Re-export stream operations with convenient names
open Stream≅Nat→ renaming (lookup to _!_; tabulate to fromFun) public

-- Prepend element to stream
infixr 5 _∷_
_∷_ : {A : Type₀} → A → Stream A → Stream A
a ∷ s = a , s

-- Constant stream
repeat : {A : Type₀} → A → Stream A
head (repeat a) = a
tail (repeat a) = repeat a

