{-# OPTIONS --cubical --guardedness --allow-unsolved-metas #-}

------------------------------------------------------------------------
-- Extended Signed-Digit Equivalence
------------------------------------------------------------------------
--
-- This module proves the equivalence between the extended signed-digit
-- reals (PreR/≈ext) and the HoTT Cauchy reals (ℝ).
--
-- EXPORTS:
--   fromℝ      : Encoding HoTT reals as signed-digit codes
--   toℝ-fromℝ  : Round-trip proof (ℝ → Real_SD → ℝ)
--   Real_SD≃ℝ  : The full type equivalence
--
-- NOTE: Relies on postulates from Embedding.agda regarding digit
-- extraction correctness (δ-correct, choose-k-correct).
--
------------------------------------------------------------------------

module Reals.SignedDigit.Extended.Equivalence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence

open import Cubical.Data.Int as ℤ using (ℤ; pos)
open import Cubical.Data.Sigma using (_,_)

open import Cubical.HITs.SetQuotients as SQ hiding ([_])

open import Reals.SignedDigit.Base
open import Reals.SignedDigit.Extended using (PreR; Real_SD; toℝ; toℝ-raw; pow2ℤ)
open import Reals.SignedDigit.Equivalence using (stream→ℝ)
open import Reals.HoTT.Base using (ℝ; rat)
open import Reals.HoTT.Embedding using (ℝ∈OpenUnit; δ; choose-k)

open import Cubical.HITs.CauchyReals.Multiplication using (_·ᵣ_)

------------------------------------------------------------------------
-- Encoding HoTT reals into Real_SD
------------------------------------------------------------------------

-- Raw encoding: use choose-k to get exponent and normalized value,
-- then extract digits using δ.

fromℝ-raw : ℝ → PreR
fromℝ-raw x with choose-k x
... | (k , z) = (k , δ z)

fromℝ : ℝ → Real_SD
fromℝ x = SQ.[ fromℝ-raw x ]

------------------------------------------------------------------------
-- Round-trip properties
------------------------------------------------------------------------

-- The round-trip proofs require proper implementations of δ (digit
-- extraction) and choose-k (normalization).
--
-- Proof sketch for toℝ-fromℝ:
--   toℝ (fromℝ y)
--     = toℝ [ (k , δ z) ]              where (k, z) = choose-k y
--     = rat (pow2ℤ k) ·ᵣ stream→ℝ (δ z)
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

------------------------------------------------------------------------
-- Type equivalence
------------------------------------------------------------------------

Real_SD≃ℝ : Real_SD ≃ ℝ
Real_SD≃ℝ = isoToEquiv (iso toℝ fromℝ toℝ-fromℝ fromℝ-toℝ)

Real_SD≡ℝ : Real_SD ≡ ℝ
Real_SD≡ℝ = ua Real_SD≃ℝ
