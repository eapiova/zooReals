{-# OPTIONS --cubical --safe --guardedness #-}

module TestLim where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals.Fast as ℚ
open import Cubical.Data.Rationals.Fast.Order as ℚ using (ℚ₊; _ℚ₊+_)
open import Cubical.HITs.CauchyReals.Base

-- Try to apply lim with an obviously wrong type to see its true type

bad : Set
bad = Set
