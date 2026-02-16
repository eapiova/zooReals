{-# OPTIONS --cubical --guardedness #-}

------------------------------------------------------------------------
-- Paper A Entrypoint: Constructive Boundary for Signed-Digit Reals
------------------------------------------------------------------------
--
-- This module is the stable reviewer-facing API for Paper A.
-- It exports only theorem statements used in the paper narrative:
--   1) constructive raw-stream limit results,
--   2) quotient-lift obstruction surface (AC_omega postulates),
--   3) logical boundary modules parameterized by H : ℝsd ≃ ℝ.

module Reals.SignedDigit.PaperA.Entrypoint where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.HITs.CauchyReals.Base using (ℝ)

open import Reals.SignedDigit.Representation using (ℝsd; toℝ)
open import Reals.SignedDigit.Safe.Limit.Core public
  using ( limA
        ; limA-eq
        ; limA-close-to-input
        )
open import Reals.SignedDigit.Safe.Limit public
  using ( limA-𝕀sd
        ; limA-𝕀sd-close
        )
open import Reals.SignedDigit.Meta.LEMBoundary public
  using ( LEM
        ; PropReflectionIntoℝ
        ; lem-from-eq-and-reflection
        )

-- Equivalence-boundary consequences for the repository interpretation map toℝ.
module AssumeEq
  (H : ℝsd ≃ ℝ)
  (H-fun≡toℝ : equivFun H ≡ toℝ)
  where
  open Reals.SignedDigit.Meta.AssumeEq H H-fun≡toℝ public
    using ( sectionℝ
          ; sectionβ
          ; sectionη
          )

module ChoiceFromEq
  (H : ℝsd ≃ ℝ)
  (H-fun≡toℝ : equivFun H ≡ toℝ)
  where
  open Reals.SignedDigit.Meta.ChoiceFromEq H H-fun≡toℝ public
    using ( familySection
          ; familySection-ℚ₊
          ; constantSection
          )
