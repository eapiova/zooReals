{-# OPTIONS --cubical --safe --guardedness #-}

------------------------------------------------------------------------
-- Coherence: rat-lim-B proof
------------------------------------------------------------------------

module Reals.SignedDigit.Safe.Equivalence.Coherence.RatLim where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals.Fast as ℚ
open import Cubical.Data.Rationals.Fast.Properties as ℚP
open import Cubical.Data.Rationals.Fast.Order as ℚO
  using (ℚ₊; ℚ₊≡; 0<_)

open import Cubical.HITs.CauchyReals.Base using (_∼[_]_)
open import Cubical.HITs.CauchyReals.Closeness using (triangle∼; sym∼)

open import Reals.SignedDigit.Safe.Bounded using (𝕀sd; ι)
open import Reals.SignedDigit.Safe.Equivalence.Arithmetic
  using (_+₊_; bound-2[e-d]+2d≡2e)
open import Reals.SignedDigit.Safe.Limit using (limA-𝕀sd; limA-𝕀sd-close)
open import Reals.SignedDigit.Safe.Equivalence.Coherence.Base

------------------------------------------------------------------------
-- rat-lim-B proof
------------------------------------------------------------------------

abstract
  rat-lim-B-proof : (q : ℚ.ℚ) (y : ℚ₊ → 𝕀sd) (ε : ℚ₊) →
                    (p : ∀ δ ε' → ι (y δ) ∼[ (δ +₊ ε') +₊ (δ +₊ ε') ] ι (y ε')) →
                    (δ : ℚ₊) →
                    (v : 0< (fst ε ℚP.- fst δ)) →
                    𝕀sd-B (ratA q) (y δ) ((fst ε ℚP.- fst δ) , v) →
                    𝕀sd-B (ratA q) (limA-𝕀sd y p) ε
  rat-lim-B-proof q y ε p δ v ih =
    subst (λ z → ι (ratA q) ∼[ z ] ι (limA-𝕀sd y p))
          bound-eq
          (triangle∼ ih lim-close-sym)
    where
      lim-close : ι (limA-𝕀sd y p) ∼[ δ +₊ δ ] ι (y δ)
      lim-close = limA-𝕀sd-close y p δ

      lim-close-sym : ι (y δ) ∼[ δ +₊ δ ] ι (limA-𝕀sd y p)
      lim-close-sym = sym∼ _ _ _ lim-close

      εmδ : ℚ₊
      εmδ = (fst ε ℚP.- fst δ , v)

      bound-eq : (εmδ +₊ εmδ) +₊ (δ +₊ δ) ≡ ε +₊ ε
      bound-eq = ℚ₊≡ (bound-2[e-d]+2d≡2e (fst ε) (fst δ))
