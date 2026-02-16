{-# OPTIONS --cubical --guardedness #-}

------------------------------------------------------------------------
-- Coherence: lim-lim-B proof
------------------------------------------------------------------------

module Reals.SignedDigit.Safe.Equivalence.Coherence.LimLim where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals.Fast as ℚ
open import Cubical.Data.Rationals.Fast.Properties as ℚP
open import Cubical.Data.Rationals.Fast.Order as ℚO
  using (ℚ₊; ℚ₊≡; 0<_)

open import Cubical.HITs.CauchyReals.Base using (_∼[_]_)
open import Cubical.HITs.CauchyReals.Closeness using (triangle∼; sym∼)

open import Reals.SignedDigit.Safe.Bounded using (𝕀sd; ι)
open import Reals.SignedDigit.Safe.Equivalence.Arithmetic
  using (_+₊_; x-[y+z]≡x-y-z; bound-2d+2[e-d-h]+2h≡2e)
open import Reals.SignedDigit.Safe.Limit using (limA-𝕀sd; limA-𝕀sd-close)
open import Reals.SignedDigit.Safe.Equivalence.Coherence.Base

------------------------------------------------------------------------
-- lim-lim-B proof
------------------------------------------------------------------------

abstract
  lim-lim-B-proof : (x y : ℚ₊ → 𝕀sd) (ε δ η : ℚ₊) →
                    (p : ∀ δ' ε' → ι (x δ') ∼[ (δ' +₊ ε') +₊ (δ' +₊ ε') ] ι (x ε')) →
                    (p' : ∀ δ' ε' → ι (y δ') ∼[ (δ' +₊ ε') +₊ (δ' +₊ ε') ] ι (y ε')) →
                    (v : 0< (fst ε ℚP.- (fst δ ℚ.+ fst η))) →
                    𝕀sd-B (x δ) (y η) ((fst ε ℚP.- (fst δ ℚ.+ fst η)) , v) →
                    𝕀sd-B (limA-𝕀sd x p) (limA-𝕀sd y p') ε
  lim-lim-B-proof x y ε δ η p p' v ih =
    subst (λ z → ι (limA-𝕀sd x p) ∼[ z ] ι (limA-𝕀sd y p'))
          bound-eq
          (triangle∼ (triangle∼ lim-x-close ih) lim-y-close-sym)
    where
      lim-x-close : ι (limA-𝕀sd x p) ∼[ δ +₊ δ ] ι (x δ)
      lim-x-close = limA-𝕀sd-close x p δ

      lim-y-close : ι (limA-𝕀sd y p') ∼[ η +₊ η ] ι (y η)
      lim-y-close = limA-𝕀sd-close y p' η

      lim-y-close-sym : ι (y η) ∼[ η +₊ η ] ι (limA-𝕀sd y p')
      lim-y-close-sym = sym∼ _ _ _ lim-y-close

      εmδη : ℚ₊
      εmδη = (fst ε ℚP.- (fst δ ℚP.+ fst η) , v)

      εmδη≡ε-δ-η : fst εmδη ≡ (fst ε ℚP.- fst δ) ℚP.- fst η
      εmδη≡ε-δ-η = x-[y+z]≡x-y-z (fst ε) (fst δ) (fst η)

      bound-eq : ((δ +₊ δ) +₊ (εmδη +₊ εmδη)) +₊ (η +₊ η) ≡ ε +₊ ε
      bound-eq = ℚ₊≡ (
        cong (λ z → ((fst δ ℚ.+ fst δ) ℚ.+ (z ℚ.+ z)) ℚ.+ (fst η ℚ.+ fst η)) εmδη≡ε-δ-η
        ∙ bound-2d+2[e-d-h]+2h≡2e (fst ε) (fst δ) (fst η))
