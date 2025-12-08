{-# OPTIONS --cubical --guardedness #-}
-- NOTE: --safe removed due to postulates for round-trip properties.
-- TODO: Implement δ and choose-k properly, then restore --safe.

-- Extended signed-digit reals built from an exponent and a raw
-- signed-digit stream. This module only sets up the basic
-- representation and equivalence relation; the interpretation into
-- the HoTT Cauchy reals is added in later steps.

module Reals.SignedDigit.Extended where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence

open import Cubical.Data.Nat as ℕ using (ℕ; zero; suc)
open import Cubical.Data.Int as ℤ using (ℤ; pos; negsuc)
open import Cubical.Data.Sigma using (Σ; _,_; _×_; fst; snd)
open import Cubical.Data.Unit
open import Cubical.Data.NatPlusOne using (ℕ₊₁; 1+_)

open import Cubical.Data.Rationals.Base as ℚᵇ renaming (ℚ to ℚˢ)
open import Cubical.Data.Rationals.Fast as ℚ hiding ([_])
open import Cubical.Data.Rationals.Fast.Order as ℚO using (ℚ₊; _ℚ₊+_; 0<_)

open import Cubical.HITs.SetQuotients as SQ hiding ([_])
open import Cubical.HITs.CauchyReals.Closeness using (isSetℝ)
open import Cubical.HITs.CauchyReals.Multiplication using (_·ᵣ_)

open import Reals.SignedDigit.Base
open import Reals.SignedDigit.Equivalence using (approx; 2^ℕ; 2^ℕ₊₁)
open import Reals.SignedDigit.Embedding using (approxF; stream→ℝ-lim)
open import Reals.HoTT.Base using (ℝ; rat; lim; _∼[_]_)
open import Reals.HoTT.Embedding using (ℝ∈OpenUnit; δ; choose-k)

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
approxExtF (k , s) n = pow2ℤ k ℚ.· approxF s n

------------------------------------------------------------------------
-- Placeholder interpretation into the HoTT Cauchy reals
------------------------------------------------------------------------

toℝ-raw : PreR → ℝ
-- Use the Cauchy-limit based embedding of streams into ℝ
-- (currently relying on the postulated Cauchy property in
--  Reals.SignedDigit.Embedding).
toℝ-raw (k , s) = rat (pow2ℤ k) ·ᵣ stream→ℝ-lim s

-- For now we quotient raw codes by the kernel of toℝ-raw, so the
-- interpretation map respects the equivalence relation by definition.

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
-- Placeholder raw encoding of HoTT reals into Real_SD
------------------------------------------------------------------------

-- We currently ignore the specific value of the input real but route
-- it through the interval/digit infrastructure. Once normalisation and
-- a genuine digit extractor are implemented, this definition will be
-- updated accordingly.

fromℝ-raw : ℝ → PreR
fromℝ-raw x with choose-k x
... | (k , z) = (k , δ z)

fromℝ : ℝ → Real_SD
fromℝ x = SQ.[ fromℝ-raw x ]

------------------------------------------------------------------------
-- Equivalence between Real_SD and ℝ
------------------------------------------------------------------------

-- The round-trip properties require proper implementations of δ (digit
-- extraction) and choose-k (normalization). With the current placeholders,
-- these are postulated. Once the TWA digit extraction algorithm is
-- implemented, these postulates can be replaced with constructive proofs.
--
-- Proof sketch for toℝ-fromℝ:
--   toℝ (fromℝ y)
--     = toℝ [ (k , δ z) ]              where (k, z) = choose-k y
--     = rat (pow2ℤ k) ·ᵣ stream→ℝ-lim (δ z)
--     = rat (pow2ℤ k) ·ᵣ val z         by δ-correct z
--     = y                               by choose-k-correct y
--
-- Proof sketch for fromℝ-toℝ:
--   For x = [ (k, s) ], need fromℝ (toℝ [ (k, s) ]) ≡ [ (k, s) ]
--   This follows from the quotient structure: since _≈ext_ is the kernel
--   of toℝ-raw, any two PreR codes mapping to the same ℝ are identified.

postulate
  -- TODO: Requires δ-correct and choose-k-correct from HoTT/Embedding
  toℝ-fromℝ : (y : ℝ) → toℝ (fromℝ y) ≡ y
  -- TODO: Follows from quotient structure once δ and choose-k are proper
  fromℝ-toℝ : (x : Real_SD) → fromℝ (toℝ x) ≡ x

Real_SD≃ℝ : Real_SD ≃ ℝ
Real_SD≃ℝ = isoToEquiv (iso toℝ fromℝ toℝ-fromℝ fromℝ-toℝ)

Real_SD≡ℝ : Real_SD ≡ ℝ
Real_SD≡ℝ = ua Real_SD≃ℝ
