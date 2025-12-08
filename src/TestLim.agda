{-# OPTIONS --cubical --safe --guardedness #-}

module TestLim where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals.Fast as ℚ
open import Cubical.Data.Rationals.Fast.Order as ℚ using (ℚ₊; _ℚ₊+_; 0<_)
open import Cubical.HITs.CauchyReals.Base

-- Reveal type of lim-lim via ill-typed definition

lim-lim-type : Set
lim-lim-type = lim-lim
