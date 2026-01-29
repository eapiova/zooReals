{-# OPTIONS --cubical --guardedness #-}

------------------------------------------------------------------------
-- Coherence: lim-rat-B proof
------------------------------------------------------------------------

module Reals.SignedDigit.Equivalence.Coherence.LimRat where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals.Fast as ℚ
open import Cubical.Data.Rationals.Fast.Properties as ℚP
open import Cubical.Data.Rationals.Fast.Order as ℚO
  using (ℚ₊; ℚ₊≡; 0<_)

open import Cubical.HITs.CauchyReals.Base using (_∼[_]_)
open import Cubical.HITs.CauchyReals.Closeness using (triangle∼)

open import Reals.SignedDigit.Bounded using (𝕀sd; ι)
open import Reals.SignedDigit.Equivalence.Arithmetic
  using (_+₊_; bound-2[e-d]+2d≡2e)
open import Reals.SignedDigit.Limit using (limA-𝕀sd; limA-𝕀sd-close)
open import Reals.SignedDigit.Equivalence.Coherence.Base

------------------------------------------------------------------------
-- lim-rat-B proof
------------------------------------------------------------------------

abstract
  lim-rat-B-proof : (x : ℚ₊ → 𝕀sd) (r : ℚ.ℚ) (ε δ : ℚ₊) →
                    (p : ∀ δ' ε' → ι (x δ') ∼[ (δ' +₊ ε') +₊ (δ' +₊ ε') ] ι (x ε')) →
                    (v : 0< (fst ε ℚP.- fst δ)) →
                    𝕀sd-B (x δ) (ratA r) ((fst ε ℚP.- fst δ) , v) →
                    𝕀sd-B (limA-𝕀sd x p) (ratA r) ε
  lim-rat-B-proof x r ε δ p v ih =
    subst (λ z → ι (limA-𝕀sd x p) ∼[ z ] ι (ratA r))
          bound-eq
          (triangle∼ lim-close ih)
    where
      lim-close : ι (limA-𝕀sd x p) ∼[ δ +₊ δ ] ι (x δ)
      lim-close = limA-𝕀sd-close x p δ

      εmδ : ℚ₊
      εmδ = (fst ε ℚP.- fst δ , v)

      bound-eq : (δ +₊ δ) +₊ (εmδ +₊ εmδ) ≡ ε +₊ ε
      bound-eq = ℚ₊≡ (ℚP.+Comm (fst δ ℚ.+ fst δ) (fst εmδ ℚ.+ fst εmδ)
                        ∙ bound-2[e-d]+2d≡2e (fst ε) (fst δ))
