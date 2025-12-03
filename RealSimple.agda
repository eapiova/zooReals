-- Definition of the real numbers with arithmetic operations and ordering

{-# OPTIONS --cubical --safe #-}

module RealSimple where


open import Data.Integer.Base as ℤ using (ℤ; +_; +0; +[1+_]; -[1+_])
import Data.Integer.Properties as ℤP
open import Data.Nat as ℕ using (ℕ; zero; suc; NonZero)
open import Level using (0ℓ)
open import Relation.Nullary
open import Relation.Nullary.Negation using (contraposition)
open import Relation.Nullary.Decidable
open import Relation.Unary using (Pred)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; _≢_; refl; cong; sym; subst; trans; ≢-sym)
open import Relation.Binary
open import Data.Rational.Unnormalised as ℚ using (ℚᵘ; mkℚᵘ; _/_; 0ℚᵘ; 1ℚᵘ; ↥_; ↧_; ↧ₙ_; _÷_; _+_; _-_; ∣_∣; _≤_; _⊔_; _⊓_)



open ℚᵘ public

record ℝ : Set where
  constructor mkℝ
  field
    -- No n≢0 condition for seq
    seq : ℕ → ℚᵘ
    reg : (m n : ℕ) .{{m≢0 : ℕ.NonZero m}} .{{n≢0 : ℕ.NonZero n}} →
             ℚ.∣ seq m ℚ.- seq n ∣ ℚ.≤
             (+ 1 ℚ./ m) ℚ.+ (+ 1 ℚ./ n)

open ℝ public

fast-reg : (x : ℝ) → (m n : ℕ) .{{m≢0 : ℕ.NonZero m}} .{{n≢0 : ℕ.NonZero n}} →
             ℚ.∣ seq x m ℚ.- seq x n ∣ ℚ.≤
             (+ 1 ℚ./ m) ℚ.+ (+ 1 ℚ./ n)
fast-reg = reg

infix 4 _≃_

data _≃_ : Rel ℝ Level.zero where
  *≃* : {x y : ℝ} → ((n : ℕ) .{{n≢0 : ℕ.NonZero n}} →
         ℚ.∣ seq x n ℚ.- seq y n ∣ ℚ.≤ (+ 2 ℚ./ n)) →
         x ≃ y