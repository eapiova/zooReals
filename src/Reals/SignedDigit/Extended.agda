{-# OPTIONS --cubical --guardedness --safe #-}

-- Extended signed-digit reals built from an exponent and a raw
-- signed-digit stream. This module sets up the basic representation
-- and equivalence relation; the full equivalence with HoTT Cauchy reals
-- requires additional structure from Reals.HoTT.Embedding which contains
-- postulates, so the equivalence proof is deferred to Extended.Equivalence.

module Reals.SignedDigit.Extended where

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

open import Reals.SignedDigit.Base
open import Reals.SignedDigit.Equivalence using (2^ℕ; 2^ℕ₊₁; approx; stream→ℝ)
open import Reals.HoTT.Base using (ℝ; rat)

------------------------------------------------------------------------
------------------------------------------------------------------------
-- Raw extended signed-digit codes and rational approximations
------------------------------------------------------------------------


-- A raw extended signed-digit code is an integer exponent together
-- with a signed-digit stream.
PreR : Type₀
PreR = ℤ × 𝟛ᴺ

-- 2^n as a Fast rational (positive exponent)
pow2ℕ : ℕ → ℚ.ℚ
pow2ℕ n = ℚ.[_/_] (ℤ.pos (2^ℕ n)) (1+ 0)

-- 2^k as a Fast rational, allowing negative exponents.
pow2ℤ : ℤ → ℚ.ℚ
pow2ℤ (pos n)    = pow2ℕ n
pow2ℤ (negsuc n) = ℚ.[_/_] (ℤ.pos 1) (2^ℕ₊₁ (suc n))

-- Extended partial sums in Fast rationals
approxExtF : PreR → ℕ → ℚ.ℚ
approxExtF (k , s) n = pow2ℤ k ℚ.· approx s n

------------------------------------------------------------------------
-- Interpretation into the HoTT Cauchy reals
------------------------------------------------------------------------

toℝ-raw : PreR → ℝ
toℝ-raw (k , s) = rat (pow2ℤ k) ·ᵣ stream→ℝ s

-- The equivalence relation on PreR is defined as the kernel of toℝ-raw.
-- This ensures that the interpretation map respects equivalence by definition.

_≈ext_ : PreR → PreR → Type₀
p ≈ext q = toℝ-raw p ≡ toℝ-raw q

toℝ-raw-resp : ∀ p q → p ≈ext q → toℝ-raw p ≡ toℝ-raw q
toℝ-raw-resp p q eq = eq

-- The type of extended signed-digit reals is the quotient of raw codes
-- by this equivalence relation.

Real_SD : Type₀
Real_SD = PreR / _≈ext_

-- Interpretation of Real_SD into the HoTT Cauchy reals.

toℝ : Real_SD → ℝ
toℝ = SQ.rec isSetℝ toℝ-raw toℝ-raw-resp

------------------------------------------------------------------------
-- The inverse direction (fromℝ) and the equivalence proof
------------------------------------------------------------------------

-- The encoding fromℝ : ℝ → Real_SD requires digit extraction (δ) and
-- normalization (choose-k) from Reals.HoTT.Embedding. That module contains
-- postulates that prevent using --safe here.
--
-- The full equivalence Real_SD ≃ ℝ is provided in Extended.Equivalence
-- (once that module has the constructive proofs).
--
-- Proof sketch for the equivalence:
--   toℝ-fromℝ : toℝ (fromℝ y) ≡ y
--     Uses δ-correct : stream→ℝ (δ z) ≡ val z
--     and choose-k-correct : relating val z back to y
--
--   fromℝ-toℝ : fromℝ (toℝ x) ≡ x
--     Follows from quotient structure since _≈ext_ is the kernel of toℝ-raw
