-- Definition of the real numbers with arithmetic operations and ordering
-- Using only the Cubical library

{-# OPTIONS --cubical --safe --guardedness #-}

module RealSimpleCubical where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

open import Cubical.Data.Int as ℤ using (ℤ; pos; neg)
open import Cubical.Data.Nat as ℕ using (ℕ; zero; suc)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Sigma

open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Data.Rationals.Properties as ℚ
open import Cubical.Data.Rationals.Order as ℚ

open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary.Base

open import Cubical.HITs.SetQuotients as SetQuotient using ([_])

open import Cubical.Data.Empty as ⊥

open import Cubical.Foundations.Prelude

-- Define NonZero predicate for natural numbers
record NonZero (n : ℕ) : Type₀ where
  field
    isNonZero : n ≡ zero → ⊥.⊥

-- Define constants for rationals
1ℚ : ℚ
1ℚ = [ pos 1 / 1+ 0 ]

2ℚ : ℚ
2ℚ = [ pos 2 / 1+ 1 ]

-- Define the absolute value function for rationals
-- |x| = max(x, -x)
∣_∣ : ℚ → ℚ
∣ x ∣ = ℚ.max x (ℚ.- x)

-- Define the real numbers as Cauchy sequences of rationals
record ℝ : Type₀ where
  constructor mkℝ
  field
    -- No n≢0 condition for seq
    seq : ℕ → ℚ
    reg : (m n : ℕ) .{{m≢0 : NonZero m}} .{{n≢0 : NonZero n}} →
             (∣ seq m ℚ.- seq n ∣) ℚ.≤
             ((1ℚ / m) ℚ.+ (1ℚ / n))

open ℝ public

fast-reg : (x : ℝ) → (m n : ℕ) .{{m≢0 : NonZero m}} .{{n≢0 : NonZero n}} →
             (∣ seq x m ℚ.- seq x n ∣) ℚ.≤
             ((1ℚ / m) ℚ.+ (1ℚ / n))
fast-reg = reg

infix 4 _≈_

data _≈_ : Rel ℝ Agda.Primitive.lzero where
 *≈* : {x y : ℝ} → ((n : ℕ) .{{n≢0 : NonZero n}} →
         (∣ seq x n ℚ.- seq y n ∣) ℚ.≤ (2ℚ / n)) →
         x ≈ y