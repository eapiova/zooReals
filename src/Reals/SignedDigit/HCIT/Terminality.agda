{-# OPTIONS --cubical --guardedness #-}

------------------------------------------------------------------------
-- Terminality of 𝕀sd among 𝕀-Algebras
------------------------------------------------------------------------
--
-- The HCIT universal property: 𝕀sd is the terminal 𝕀-Algebra.
-- For any 𝕀-Algebra A, there exists a unique 𝕀-Hom from A to 𝕀sd.
--
-- KNOWN OBSTRUCTION: The semantics map sem : A.Carrier → ℝ requires
-- decomposing elements via gen (which gives only truncated existence)
-- and recursing on the decomposition. This requires AC_ω (countable
-- dependent choice), which is unavailable constructively.
-- See also: Safe/Limit.agda for the same obstruction in a different
-- context.
--
-- Strategy:
--   1. Postulate sem : A.Carrier → ℝ with its defining equation
--   2. Define morph : A.Carrier → 𝕀sd via ι⁻¹ ∘ sem
--   3. Show morph is an 𝕀-Hom (preserves cons, inc, dec)
--   4. Show uniqueness (any 𝕀-Hom A 𝕀sd equals morph)
--
-- POSTULATE INVENTORY:
--
-- Name             | File             | AC_ω? | Reason
-- -----------------|------------------|-------|------------------------------------------
-- inc-resp         | IncDec.agda      | No    | Semantic: stream→ℝ(inc s) relates to s
-- dec-resp         | IncDec.agda      | No    | Semantic: stream→ℝ(dec s) relates to s
-- carry-raw        | IncDec.agda      | No    | Semantic: both sides same ℝ value
-- borrow-raw       | IncDec.agda      | No    | Semantic: both sides same ℝ value
-- cons-resp        | Structure.agda   | No    | Semantic: stream→ℝ(d∷s) relates to s
-- inc⁻¹-𝕀 (×6)    | Structure.agda   | No    | Semantic: both sides same ℝ value
-- carry-compl-𝕀    | Structure.agda   | No    | Semantic: ℝ arithmetic implication
-- borrow-compl-𝕀   | Structure.agda   | No    | Semantic: ℝ arithmetic implication
-- sep-L-𝕀         | Structure.agda   | No    | Semantic: ℝ arithmetic implication
-- sep-R-𝕀         | Structure.agda   | No    | Semantic: ℝ arithmetic implication
-- sem              | Terminality.agda | YES   | Decomposing via gen requires AC_ω
-- sem-cons         | Terminality.agda | YES   | Part of sem specification
-- sem-𝕀sd          | Terminality.agda | YES   | Part of sem specification
-- ι⁻¹             | Terminality.agda | NO*   | Exists via ℝsd≃ℝ but not imported
-- ι-section        | Terminality.agda | NO*   | Part of ι⁻¹ specification
-- ι-retract        | Terminality.agda | NO*   | Part of ι⁻¹ specification
-- morph-is-hom     | Terminality.agda | YES   | Depends on sem-cons
-- morph-unique     | Terminality.agda | YES   | Depends on sem
--
-- NO* = not inherently AC_ω, but not imported from Equivalence.agda

module Reals.SignedDigit.HCIT.Terminality where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

open import Cubical.HITs.SetQuotients as SQ

open import Cubical.HITs.CauchyReals.Base using (ℝ; rat; lim; eqℝ)
open import Cubical.HITs.CauchyReals.Closeness using (isSetℝ)
open import Cubical.HITs.CauchyReals.Order using (_+ᵣ_)
open import Cubical.HITs.CauchyReals.Multiplication using (/2ᵣ)

open import Reals.SignedDigit.Core
open import Reals.SignedDigit.Bounded
  using ( stream→ℝ; _≈sd_; 𝕀sd; [_]sd; isSet𝕀sd; ι
        ; digitToℚ )
open import Reals.SignedDigit.IncDec
open import Reals.SignedDigit.HCIT.Algebra
open import Reals.SignedDigit.HCIT.Structure using (𝕀sd-Alg; cons𝕀)

------------------------------------------------------------------------
-- Injectivity of ι
------------------------------------------------------------------------
-- ι : 𝕀sd → ℝ is injective because _≈sd_ is defined as
-- stream→ℝ s ≡ stream→ℝ t, so eq/ gives us the quotient path
-- whenever the images agree.

ι-inj : (a b : 𝕀sd) → ι a ≡ ι b → a ≡ b
ι-inj = SQ.elimProp2 (λ _ _ → isPropΠ (λ _ → isSet𝕀sd _ _))
  (λ s t h → eq/ s t h)

------------------------------------------------------------------------
-- Semantics map (POSTULATE: requires AC_ω)
------------------------------------------------------------------------
-- For any 𝕀-Algebra A, sem assigns a real number to each element.
-- Intuitively: sem (cons d x) = (digitToℚ d + sem x) / 2.
-- Construction requires iterating gen to decompose elements, choosing
-- representatives from truncated existentials — hence AC_ω.

postulate
  -- POSTULATE: requires AC_ω (countable dependent choice)
  sem : (A : 𝕀-Alg) → 𝕀-Alg.Carrier A → ℝ

  -- The defining equation: sem(cons d x) = (digitToℚ d + sem x) / 2
  sem-cons : (A : 𝕀-Alg) (d : Digit) (x : 𝕀-Alg.Carrier A)
           → sem A (𝕀-Alg.cons A d x) ≡ /2ᵣ (rat (digitToℚ d) +ᵣ sem A x)

  -- sem for 𝕀sd-Alg agrees with ι
  sem-𝕀sd : (x : 𝕀sd) → sem 𝕀sd-Alg x ≡ ι x

------------------------------------------------------------------------
-- The unique morphism A → 𝕀sd
------------------------------------------------------------------------

-- POSTULATE: the inverse map ℝ → 𝕀sd
-- This exists because 𝕀sd ≃ ℝ (via the surjection approach in
-- Equivalence.agda), but constructing it requires going through
-- the full equivalence proof.
postulate
  ι⁻¹ : ℝ → 𝕀sd
  ι-section : (x : ℝ) → ι (ι⁻¹ x) ≡ x
  ι-retract : (x : 𝕀sd) → ι⁻¹ (ι x) ≡ x

-- The canonical morphism from any 𝕀-Algebra to 𝕀sd
morph : (A : 𝕀-Alg) → 𝕀-Alg.Carrier A → 𝕀sd
morph A a = ι⁻¹ (sem A a)

-- morph is an 𝕀-Hom (POSTULATE: requires sem-cons and ℝ arithmetic)
postulate
  morph-is-hom : (A : 𝕀-Alg) → 𝕀-Hom A 𝕀sd-Alg

------------------------------------------------------------------------
-- Uniqueness
------------------------------------------------------------------------
-- Any 𝕀-Hom f : A → 𝕀sd equals morph A.
--
-- Argument: f preserves cons, inc, dec. Since ι is injective and
-- both ι ∘ f and sem satisfy the same recursive equation
-- (value at cons d x = d/2 + value at x / 2), they must agree.
-- So f = ι⁻¹ ∘ ι ∘ f = ι⁻¹ ∘ sem = morph.

postulate
  morph-unique : (A : 𝕀-Alg) (f : 𝕀-Hom A 𝕀sd-Alg)
               → ∀ (a : 𝕀-Alg.Carrier A)
               → 𝕀-Hom.map f a ≡ morph A a

------------------------------------------------------------------------
-- Terminal object statement
------------------------------------------------------------------------

-- 𝕀sd-Alg is terminal: for any A, there is a unique morphism A → 𝕀sd.
-- The type of 𝕀-Homs from A to 𝕀sd-Alg is contractible.

isTerminal-𝕀sd : (A : 𝕀-Alg) → isContr (𝕀-Hom A 𝕀sd-Alg)
isTerminal-𝕀sd A = morph-is-hom A , λ f →
  𝕀-Hom-path (morph-is-hom A) f
    (λ a → morph-unique A (morph-is-hom A) a ∙ sym (morph-unique A f a))
