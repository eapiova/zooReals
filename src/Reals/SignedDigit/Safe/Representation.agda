{-# OPTIONS --cubical --safe --guardedness #-}

module Reals.SignedDigit.Safe.Representation where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat as ℕ using (ℕ ; zero ; suc ; _·_)
open import Cubical.Data.Int as ℤ using (ℤ ; pos ; negsuc)
open import Cubical.Data.NatPlusOne using (1+_)
open import Cubical.Data.Rationals.Fast as ℚ hiding ([_])

open import Cubical.HITs.CauchyReals.Base using (ℝ)
open import Cubical.HITs.CauchyReals.Closeness using (isSetℝ)

2^ℕ : ℕ → ℕ
2^ℕ zero = 1
2^ℕ (suc n) = 2 ℕ.· 2^ℕ n

pow2ℕ : ℕ → ℚ.ℚ
pow2ℕ n = ℚ.[_/_] (ℤ.pos (2^ℕ n)) (1+ 0)

pow2ℤ : ℤ → ℚ.ℚ
pow2ℤ (pos n) = pow2ℕ n
pow2ℤ (negsuc n) = ℚ.[_/_] (ℤ.pos 1) (1+ n)

ℝsd-raw : Type₀
ℝsd-raw = ℝ

ℝsd : Type₀
ℝsd = ℝ

isSetℝsd : isSet ℝsd
isSetℝsd = isSetℝ

toℝ-raw : ℝsd-raw → ℝ
toℝ-raw x = x

toℝ : ℝsd → ℝ
toℝ x = x
