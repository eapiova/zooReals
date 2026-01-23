{-# OPTIONS --cubical --guardedness #-}

------------------------------------------------------------------------
-- Coherence Proofs for Signed-Digit Equivalence
------------------------------------------------------------------------
--
-- This module contains the slow coherence proofs (rat-rat-B, rat-lim-B,
-- lim-rat-B, lim-lim-B) extracted for separate compilation and caching.
--
------------------------------------------------------------------------

module Reals.SignedDigit.Equivalence.Coherence where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Int as ℤ using (ℤ; pos)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.HITs.SetQuotients as SQ hiding ([_])
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Data.Rationals.Fast as ℚ
open import Cubical.Data.Rationals.Fast.Properties as ℚP
open import Cubical.Data.Rationals.Fast.Order as ℚO
  using (ℚ₊; minus-<; isTrans<≤; isTrans<; ℚ₊≡; 0<ℚ₊)
open import Cubical.Data.Rationals.Fast.Order.Properties as ℚOP
  using (/2₊)

open import Cubical.HITs.CauchyReals.Base as ℝBase using (ℝ; rat; _∼[_]_; rat-rat-fromAbs)
open import Cubical.HITs.CauchyReals.Closeness using (triangle∼; sym∼)

open import Reals.SignedDigit.Core
open import Reals.SignedDigit.Bounded using (𝕀sd; isSet𝕀sd; stream→ℝ; rational→stream; clampℚ; clamp-lip; ι; 0ℚ)
open import Reals.SignedDigit.Equivalence.RoundTrip using (round-trip-clamped)
open import Reals.SignedDigit.Equivalence.Arithmetic
  using (_+₊_; bound-2[e-d]+2d≡2e; x-[y+z]≡x-y-z; bound-2d+2[e-d-h]+2h≡2e)
open import Reals.SignedDigit.Limit using (limA-𝕀sd; limA-𝕀sd-close)

------------------------------------------------------------------------
-- Abstract helpers to prevent term explosion
------------------------------------------------------------------------

abstract
  neg-flip : (a e : ℚ.ℚ) → (ℚP.- e) ℚO.< a → (ℚP.- a) ℚO.< e
  neg-flip a e proof = subst ((ℚP.- a) ℚO.<_) (ℚP.-Invol e) (minus-< (ℚP.- e) a proof)

  max<→ : (a b c : ℚ.ℚ) → a ℚO.< c → b ℚO.< c → ℚP.max a b ℚO.< c
  max<→ a b c a<c b<c = PT.rec (ℚO.isProp< (ℚP.max a b) c) handle (ℚO.isTotal≤ a b)
    where
      handle : (a ℚO.≤ b) ⊎ (b ℚO.≤ a) → ℚP.max a b ℚO.< c
      handle (inl a≤b) = subst (ℚO._< c) (sym (ℚO.≤→max a b a≤b)) b<c
      handle (inr b≤a) = subst (ℚO._< c) (sym (ℚP.maxComm a b ∙ ℚO.≤→max b a b≤a)) a<c

  ε<2ε : (ε : ℚ₊) → fst ε ℚO.< fst (ε +₊ ε)
  ε<2ε ε = subst (ℚO._< (fst ε ℚ.+ fst ε)) (ℚP.+IdR (fst ε))
                 (ℚO.<-o+ 0ℚ (fst ε) (fst ε) (0<ℚ₊ ε))

------------------------------------------------------------------------
-- rat-rat-B proof
------------------------------------------------------------------------

-- Type alias for B relation
𝕀sd-B : 𝕀sd → 𝕀sd → ℚ₊ → Type₀
𝕀sd-B a a' ε = ι a ∼[ ε +₊ ε ] ι a'

-- ratA helper
ratA : ℚ.ℚ → 𝕀sd
ratA q = SQ.[ rational→stream q ]

abstract
  rat-rat-B-proof : (q r : ℚ.ℚ) (ε : ℚ₊) →
                    (ℚP.- fst ε) ℚO.< (q ℚP.- r) →
                    (q ℚP.- r) ℚO.< fst ε →
                    𝕀sd-B (ratA q) (ratA r) ε
  rat-rat-B-proof q r ε vₗ vᵤ =
    subst2 (λ a b → a ∼[ ε +₊ ε ] b) (sym (round-trip-clamped q)) (sym (round-trip-clamped r))
           (rat-rat-fromAbs (clampℚ q) (clampℚ r) (ε +₊ ε) clamped-bound-2ε)
    where
      x : ℚ.ℚ
      x = q ℚP.- r
      ε' : ℚ.ℚ
      ε' = fst ε

      neg-x<ε : (ℚP.- x) ℚO.< ε'
      neg-x<ε = neg-flip x ε' vₗ

      abs-bound : ℚP.abs x ℚO.< ε'
      abs-bound = max<→ x (ℚP.- x) ε' vᵤ neg-x<ε

      clamped-bound : ℚP.abs (clampℚ q ℚP.- clampℚ r) ℚO.< ε'
      clamped-bound = ℚO.isTrans≤< _ _ _ (clamp-lip q r) abs-bound

      clamped-bound-2ε : ℚP.abs (clampℚ q ℚP.- clampℚ r) ℚO.< fst (ε +₊ ε)
      clamped-bound-2ε = ℚO.isTrans< _ _ _ clamped-bound (ε<2ε ε)

------------------------------------------------------------------------
-- rat-lim-B proof
------------------------------------------------------------------------

abstract
  rat-lim-B-proof : (q : ℚ.ℚ) (y : ℚ₊ → 𝕀sd) (ε : ℚ₊) →
                    (p : ∀ δ ε' → ι (y δ) ∼[ (δ +₊ ε') +₊ (δ +₊ ε') ] ι (y ε')) →
                    (δ : ℚ₊) →
                    (v : ℚO.0< (fst ε ℚP.- fst δ)) →
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
      bound-eq = ℚO.ℚ₊≡ (bound-2[e-d]+2d≡2e (fst ε) (fst δ))

------------------------------------------------------------------------
-- lim-rat-B proof
------------------------------------------------------------------------

abstract
  lim-rat-B-proof : (x : ℚ₊ → 𝕀sd) (r : ℚ.ℚ) (ε δ : ℚ₊) →
                    (p : ∀ δ' ε' → ι (x δ') ∼[ (δ' +₊ ε') +₊ (δ' +₊ ε') ] ι (x ε')) →
                    (v : ℚO.0< (fst ε ℚP.- fst δ)) →
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
      bound-eq = ℚO.ℚ₊≡ (ℚP.+Comm (fst δ ℚ.+ fst δ) (fst εmδ ℚ.+ fst εmδ)
                          ∙ bound-2[e-d]+2d≡2e (fst ε) (fst δ))

------------------------------------------------------------------------
-- lim-lim-B proof
------------------------------------------------------------------------

abstract
  lim-lim-B-proof : (x y : ℚ₊ → 𝕀sd) (ε δ η : ℚ₊) →
                    (p : ∀ δ' ε' → ι (x δ') ∼[ (δ' +₊ ε') +₊ (δ' +₊ ε') ] ι (x ε')) →
                    (p' : ∀ δ' ε' → ι (y δ') ∼[ (δ' +₊ ε') +₊ (δ' +₊ ε') ] ι (y ε')) →
                    (v : ℚO.0< (fst ε ℚP.- (fst δ ℚ.+ fst η))) →
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
      bound-eq = ℚO.ℚ₊≡ (
        cong (λ z → ((fst δ ℚ.+ fst δ) ℚ.+ (z ℚ.+ z)) ℚ.+ (fst η ℚ.+ fst η)) εmδη≡ε-δ-η
        ∙ bound-2d+2[e-d-h]+2h≡2e (fst ε) (fst δ) (fst η))
