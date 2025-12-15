{-# OPTIONS --cubical --guardedness #-}

-- Full (Unbounded) Signed-Digit Reals
--
-- This module sets up the basic representation and equivalence relation
-- for signed-digit reals with integer exponents (x * 2^k).
--
-- The full equivalence with HoTT Cauchy reals is provided in 
-- Reals.SignedDigit.Equivalence.

module Reals.SignedDigit.Representation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat as ℕ using (ℕ; zero; suc)
open import Cubical.Data.Int as ℤ using (ℤ; pos; negsuc)
open import Cubical.Data.Sigma using (Σ; _,_; _×_; fst; snd)
open import Cubical.Data.NatPlusOne using (ℕ₊₁; 1+_)

open import Cubical.Data.Rationals.Fast as ℚ hiding ([_])

open import Cubical.HITs.SetQuotients as SQ hiding ([_])
open import Cubical.HITs.CauchyReals.Closeness using (isSetℝ)
open import Cubical.HITs.CauchyReals.Multiplication using (_·ᵣ_)

open import Reals.SignedDigit.Core
open import Reals.SignedDigit.Bounded using (2^ℕ; 2^ℕ₊₁; approx; stream→ℝ)
open import Cubical.HITs.CauchyReals.Base using (ℝ; rat)

------------------------------------------------------------------------
------------------------------------------------------------------------
-- Raw extended signed-digit codes and rational approximations
------------------------------------------------------------------------


-- A raw extended signed-digit code is an integer exponent together
-- with a signed-digit stream.
ℝsd-raw : Type₀
ℝsd-raw = ℤ × 𝟛ᴺ

-- 2^n as a Fast rational (positive exponent)
pow2ℕ : ℕ → ℚ.ℚ
pow2ℕ n = ℚ.[_/_] (ℤ.pos (2^ℕ n)) (1+ 0)

-- 2^k as a Fast rational, allowing negative exponents.
pow2ℤ : ℤ → ℚ.ℚ
pow2ℤ (pos n)    = pow2ℕ n
pow2ℤ (negsuc n) = ℚ.[_/_] (ℤ.pos 1) (2^ℕ₊₁ (suc n))

-- Extended partial sums in Fast rationals
approxExtF : ℝsd-raw → ℕ → ℚ.ℚ
approxExtF (k , s) n = pow2ℤ k ℚ.· approx s n

------------------------------------------------------------------------
-- Interpretation into the HoTT Cauchy reals
------------------------------------------------------------------------

toℝ-raw : ℝsd-raw → ℝ
toℝ-raw (k , s) = rat (pow2ℤ k) ·ᵣ stream→ℝ s

-- The equivalence relation on ℝsd-raw is defined as the kernel of toℝ-raw.
-- This ensures that the interpretation map respects equivalence by definition.

_≈ext_ : ℝsd-raw → ℝsd-raw → Type₀
p ≈ext q = toℝ-raw p ≡ toℝ-raw q

toℝ-raw-resp : ∀ p q → p ≈ext q → toℝ-raw p ≡ toℝ-raw q
toℝ-raw-resp p q eq = eq

-- The type of extended signed-digit reals is the quotient of raw codes
-- by this equivalence relation.

ℝsd : Type₀
ℝsd = ℝsd-raw / _≈ext_

isSetℝsd : isSet ℝsd
isSetℝsd = SQ.squash/

-- Interpretation of ℝsd into the HoTT Cauchy reals.

toℝ : ℝsd → ℝ
toℝ = SQ.rec isSetℝ toℝ-raw toℝ-raw-resp

------------------------------------------------------------------------
-- The inverse direction (fromℝ) and the equivalence proof
------------------------------------------------------------------------

-- The encoding fromℝ : ℝ → ℝsd requires digit extraction and normalization.
-- These are implemented in Reals.SignedDigit.Equivalence.
--
-- The full equivalence ℝsd ≃ ℝ is provided in Equivalence.agda.equivalence:
--   toℝ-fromℝ : toℝ (fromℝ y) ≡ y
--     Uses δ-correct : stream→ℝ (δ z) ≡ val z
--     and choose-k-correct : relating val z back to y
--
--   fromℝ-toℝ : fromℝ (toℝ x) ≡ x
--   fromℝ-toℝ : fromℝ (toℝ x) ≡ x
--     Follows from quotient structure since _≈ext_ is the kernel of toℝ-raw
