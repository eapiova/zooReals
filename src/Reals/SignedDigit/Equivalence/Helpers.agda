{-# OPTIONS --cubical --guardedness #-}

------------------------------------------------------------------------
-- Signed-Digit Equivalence: Helper Definitions
------------------------------------------------------------------------
--
-- Common imports and helper definitions used across the equivalence
-- modules.
--
------------------------------------------------------------------------

module Reals.SignedDigit.Equivalence.Helpers where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence

open import Cubical.Data.Nat as ℕ using (ℕ; zero; suc)
open import Cubical.Data.Int as ℤ using (ℤ; pos; negsuc)
open import Cubical.Data.Sigma hiding (_,_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.NatPlusOne
open import Cubical.Codata.Stream using (_,_; Stream)
open import Cubical.Data.Rationals.Fast as ℚ
open import Cubical.Data.Rationals.Fast.Properties as ℚP
open import Cubical.Data.Rationals.Fast.Order as ℚO
  using (ℚ₊; Trichotomy; _≟_; lt; eq; gt; isTrans<; <-o+; isTotal≤; isProp<; minus-<)
open import Cubical.Data.Rationals.Fast.Order.Properties as ℚOrderProps

-- Alias ℚF for compatibility with merged code
module ℚF = ℚ
module ℚFO = ℚO
module ℚFOP = ℚOrderProps

open import Cubical.Data.Rationals.Base as ℚˢ renaming (ℚ to ℚˢ)
open import Cubical.Data.Rationals.Properties as ℚˢP using (_+_)

open import Cubical.HITs.SetQuotients as SQ hiding ([_])
open import Cubical.HITs.CauchyReals.Order as ℝO
  using (clampᵣ; _+ᵣ_; -ᵣ_; _-ᵣ_; minᵣ; maxᵣ; _<ᵣ_; isProp<ᵣ)
open import Cubical.HITs.CauchyReals.Multiplication as ℝMul using (_·ᵣ_; ·IdL)
open import Cubical.HITs.CauchyReals.Closeness using (isSetℝ; refl∼)
open import Cubical.HITs.CauchyReals.Continuous using (limConstRat)
open import Cubical.HITs.PropositionalTruncation as PT

open import Reals.SignedDigit.Core
open import Reals.SignedDigit.Bounded using (𝕀sd; _≈sd_; isSet𝕀sd; approx; stream→ℝ; approxℚ₊; approxℚ₊-cauchy; inv2^; digitContrib; digitToℚ; rational→stream; clampℚ; weak-ineq; -1ℚ; +1ℚ; rational→stream-clamp-eq; clamp-lip; ι)
open import Reals.SignedDigit.Representation using (ℝsd-raw; ℝsd; toℝ; toℝ-raw; pow2ℤ; isSetℝsd)
open import Cubical.HITs.CauchyReals.Base using (ℝ; rat; lim; eqℝ; _∼[_]_; lim-lim; rat-rat-fromAbs; Elimℝ-Prop)

------------------------------------------------------------------------
-- Core Embedding Logic (ℝ → 𝕀sd)
------------------------------------------------------------------------

-- Open interval type representing values conceptually in (-1,1).
-- Currently uses Unit as a placeholder proof component.
ℝ∈OpenUnit : Type₀
ℝ∈OpenUnit = Σ ℝ (λ _ → Unit)

val : ℝ∈OpenUnit → ℝ
val (x , _) = x

-- Canonical endpoints -1 and +1 in ℝ (HoTT Cauchy reals)
minusOneℝ : ℝ
minusOneℝ = rat (ℚ.[ ℤ.negsuc 0 / 1+ 0 ])

oneℝ : ℝ
oneℝ = rat (ℚ.[ ℤ.pos 1 / 1+ 0 ])

-- Normalisation: choose an integer exponent and an element of the
-- conceptual open unit interval. At this stage we only clamp the
-- input real into the closed interval [-1, 1] and always return
-- exponent 0; once a genuine scaling argument is implemented, this
-- definition will be refined so that x ≡ 2^k · val z with |val z| < 1.
choose-k : ℝ → ℤ × ℝ∈OpenUnit
choose-k x = (pos 0 , (clampᵣ minusOneℝ oneℝ x , tt))

-- 1 as ℚ₊ for fixed precision in limit case
1ℚ₊ : ℚ₊
1ℚ₊ = ℚF.fromNat 1 , ℚFO.<→0< _ (ℚFOP.0<sucN 0)
