{-# OPTIONS --cubical --safe --guardedness #-}

module Reals.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Function
open import Cubical.Foundations.SIP

open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Data.Int
open import Cubical.Data.Rationals
open import Cubical.Data.Nat.Literals

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetQuotients as SQ

-- Rational number literals
0# : ℚ
0# = 0

1# : ℚ
1# = 1

2# : ℚ
2# = 2
-- Common notation and utilities for real numbers