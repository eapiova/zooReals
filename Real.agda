-- Definition of the real numbers with arithmetic operations and ordering

{-# OPTIONS --without-K --safe #-}

module Real where

open import Algebra
open import Data.Bool.Base using (Bool; if_then_else_)
open import Function.Base using (_∘_)
open import Data.Integer.Base as ℤ using (ℤ; +_; +0; +[1+_]; -[1+_])
import Data.Integer.Properties as ℤP
open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Nat.Properties as ℕP using (≤-step)
import Data.Nat.DivMod as ℕD
open import Level using (0ℓ)
open import Data.Product
open import Relation.Nullary
open import Relation.Nullary.Negation using (contraposition)
open import Relation.Nullary.Decidable
open import Relation.Unary using (Pred)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; _≢_; refl; cong; sym; subst; trans; ≢-sym)
open import Relation.Binary
open import Data.Rational.Unnormalised as ℚ using (ℚᵘ; mkℚᵘ; _/_; 0ℚᵘ; 1ℚᵘ; ↥_; ↧_; ↧ₙ_; NonZero)
import Data.Rational.Unnormalised.Properties as ℚP
open import Algebra.Bundles
open import Algebra.Structures
open import Data.Empty
open import Data.Sum
open import Data.Maybe.Base
import NonReflectiveQ as ℚ-Solver
import NonReflectiveZ as ℤ-Solver
open import Data.List


open ℚᵘ public

record ℝ : Set where
  constructor mkℝ
  field
    -- No n≢0 condition for seq
    seq : ℕ → ℚᵘ
    reg : (m n : ℕ) {m≢0 : m NonZero} {n≢0 : n NonZero} →
            ℚ.∣ seq m ℚ.- seq n ∣ ℚ.≤
            (+ 1 / m) {m≢0} ℚ.+ (+ 1 / n) {n≢0}

open ℝ public

abstract
  fast-reg : (x : ℝ) → (m n : ℕ) {m≢0 : m NonZero} {n≢0 : n NonZero} →
            ℚ.∣ seq x m ℚ.- seq x n ∣ ℚ.≤
            (+ 1 / m) {m≢0} ℚ.+ (+ 1 / n) {n≢0} 
  fast-reg = reg

infix 4 _≃_
infixl 6 _+_ _-_ _⊔_ _⊓_ _⊓₂_
infixl 7 _*_
infix 8 -_ _⋆

data _≃_ : Rel ℝ Level.zero where
  *≃* : {x y : ℝ} → ((n : ℕ) {n≢0 : n NonZero} →
        ℚ.∣ seq x n ℚ.- seq y n ∣ ℚ.≤ (+ 2 / n) {n≢0}) →
        x ≃ y

