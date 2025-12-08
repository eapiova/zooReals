{-# OPTIONS --cubical --safe --guardedness #-}

-- Signed-digit representation of real numbers in [-1, 1]
-- Based on TWA Thesis Chapter 5 (TypeTopology), ported to Cubical Agda

module Reals.SignedDigit.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat as ℕ using (ℕ; zero; suc)
open import Cubical.Data.Int as ℤ using (ℤ; pos; negsuc)
open import Cubical.Data.Sigma

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
  where open import Cubical.Data.Empty as ⊥
discreteDigit -1d +1d = no (λ p → subst (λ { -1d → Digit ; 0d → ⊥ ; +1d → ⊥ }) p -1d)
  where open import Cubical.Data.Empty as ⊥
discreteDigit 0d -1d  = no (λ p → subst (λ { -1d → ⊥ ; 0d → Digit ; +1d → ⊥ }) p 0d)
  where open import Cubical.Data.Empty as ⊥
discreteDigit 0d 0d   = yes refl
discreteDigit 0d +1d  = no (λ p → subst (λ { -1d → ⊥ ; 0d → Digit ; +1d → ⊥ }) p 0d)
  where open import Cubical.Data.Empty as ⊥
discreteDigit +1d -1d = no (λ p → subst (λ { -1d → ⊥ ; 0d → ⊥ ; +1d → Digit }) p +1d)
  where open import Cubical.Data.Empty as ⊥
discreteDigit +1d 0d  = no (λ p → subst (λ { -1d → ⊥ ; 0d → ⊥ ; +1d → Digit }) p +1d)
  where open import Cubical.Data.Empty as ⊥
discreteDigit +1d +1d = yes refl

-- Digit is a set (discrete types are sets)
isSetDigit : isSet Digit
isSetDigit = Discrete→isSet discreteDigit

-- Negation on digits
flip : Digit → Digit
flip -1d = +1d
flip 0d  = 0d
flip +1d = -1d

-- Convert digit to integer: -1 ↦ -1, 0 ↦ 0, +1 ↦ +1
digitToℤ : Digit → ℤ
digitToℤ -1d = negsuc 0    -- -1
digitToℤ 0d  = pos 0       -- 0
digitToℤ +1d = pos 1       -- +1

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

------------------------------------------------------------------------
-- Negation on signed-digit sequences
------------------------------------------------------------------------

-- Negate a signed-digit sequence (represents -x)
neg : 𝟛ᴺ → 𝟛ᴺ
neg = mapS flip
