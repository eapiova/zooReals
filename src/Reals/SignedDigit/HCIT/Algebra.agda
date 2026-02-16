{-# OPTIONS --cubical #-}

------------------------------------------------------------------------
-- HCIT Algebra Signature for Signed-Digit Reals
------------------------------------------------------------------------
--
-- Following Altenkirch's FINAL formulation (slides 13, 14, 18):
-- An 𝕀-Algebra is a type equipped with:
--   • cons : Digit → X → X
--   • inc, dec : X → X  (carry/borrow propagation)
--   • equations governing inc/dec behaviour
--   • generation: every element is a cons
--   • completeness/separation: characterising cross-head equalities
--
-- NOTE: no-conf (slide 10) is OMITTED — it is false in the quotient
-- model 𝕀sd. Counterexample: [-1 ∷ oneStream] ≡ [+1 ∷ negOneStream]
-- since both represent 0. The completeness/separation equations from
-- slides 14 and 18 replace it.
--
-- The carry/borrow equations:
--   carry  : cons +1 (cons -1 x) ≡ cons 0 (inc x)
--   borrow : cons -1 (cons +1 x) ≡ cons 0 (dec x)
-- are included as fields since derivability from completeness + separation
-- is nontrivial for general algebras.

module Reals.SignedDigit.HCIT.Algebra where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.HITs.PropositionalTruncation using (∥_∥₁)

open import Cubical.Data.Sigma

open import Reals.SignedDigit.Core using (Digit; -1d; 0d; +1d)

------------------------------------------------------------------------
-- 𝕀-Algebra
------------------------------------------------------------------------

record 𝕀-Alg : Type₁ where
  field
    Carrier : Type₀
    isSetCarrier : isSet Carrier

    -- Operations
    cons : Digit → Carrier → Carrier
    inc  : Carrier → Carrier
    dec  : Carrier → Carrier

    ---------------------------------------------------------------
    -- inc/dec defining equations (slide 13)
    ---------------------------------------------------------------
    -- inc distributes over cons by propagating or absorbing carry
    inc⁻¹ : ∀ x → inc (cons -1d x) ≡ cons 0d (inc x)
    inc⁰  : ∀ x → inc (cons  0d x) ≡ cons +1d (cons 0d x)
    inc⁺¹ : ∀ x → inc (cons +1d x) ≡ cons +1d (inc x)

    -- dec distributes over cons by propagating or absorbing borrow
    dec⁺¹ : ∀ x → dec (cons +1d x) ≡ cons  0d (dec x)
    dec⁰  : ∀ x → dec (cons  0d x) ≡ cons -1d (cons 0d x)
    dec⁻¹ : ∀ x → dec (cons -1d x) ≡ cons -1d (dec x)

    ---------------------------------------------------------------
    -- Carry/borrow equations
    ---------------------------------------------------------------
    carry  : ∀ x → cons +1d (cons -1d x) ≡ cons 0d (inc x)
    borrow : ∀ x → cons -1d (cons +1d x) ≡ cons 0d (dec x)

    ---------------------------------------------------------------
    -- Generation (every element decomposes as a cons)
    ---------------------------------------------------------------
    gen : ∀ y → ∥ Σ[ d ∈ Digit ] Σ[ x ∈ Carrier ] (y ≡ cons d x) ∥₁

    ---------------------------------------------------------------
    -- Carry/borrow completeness (slide 14)
    ---------------------------------------------------------------
    -- Cross-head equalities through 0 are exactly carry/borrow
    carry-compl  : ∀ x y → cons 0d x ≡ inc y → cons -1d x ≡ cons 0d y
    borrow-compl : ∀ x y → cons 0d x ≡ dec y → cons +1d x ≡ cons 0d y

    ---------------------------------------------------------------
    -- Separation (slide 18) — reverse directions
    ---------------------------------------------------------------
    sep-L : ∀ x y → cons -1d x ≡ cons 0d y → cons 0d x ≡ inc y
    sep-R : ∀ x y → cons +1d x ≡ cons 0d y → cons 0d x ≡ dec y


------------------------------------------------------------------------
-- 𝕀-Algebra morphisms
------------------------------------------------------------------------

record 𝕀-Hom (A B : 𝕀-Alg) : Type₀ where
  private
    module A = 𝕀-Alg A
    module B = 𝕀-Alg B

  field
    map : A.Carrier → B.Carrier
    map-cons : ∀ d x → map (A.cons d x) ≡ B.cons d (map x)
    map-inc  : ∀ x → map (A.inc x) ≡ B.inc (map x)
    map-dec  : ∀ x → map (A.dec x) ≡ B.dec (map x)

  -- Preservation of gen, carry-compl, borrow-compl, sep-L, sep-R
  -- follows automatically: these are propositions (equalities in a set
  -- or truncations), so any two proofs are equal.

------------------------------------------------------------------------
-- Identity and composition
------------------------------------------------------------------------

𝕀-id : (A : 𝕀-Alg) → 𝕀-Hom A A
𝕀-Hom.map (𝕀-id A) x = x
𝕀-Hom.map-cons (𝕀-id A) d x = refl
𝕀-Hom.map-inc (𝕀-id A) x = refl
𝕀-Hom.map-dec (𝕀-id A) x = refl

𝕀-comp : {A B C : 𝕀-Alg} → 𝕀-Hom A B → 𝕀-Hom B C → 𝕀-Hom A C
𝕀-Hom.map (𝕀-comp f g) x = 𝕀-Hom.map g (𝕀-Hom.map f x)
𝕀-Hom.map-cons (𝕀-comp f g) d x =
  cong (𝕀-Hom.map g) (𝕀-Hom.map-cons f d x) ∙ 𝕀-Hom.map-cons g d _
𝕀-Hom.map-inc (𝕀-comp f g) x =
  cong (𝕀-Hom.map g) (𝕀-Hom.map-inc f x) ∙ 𝕀-Hom.map-inc g _
𝕀-Hom.map-dec (𝕀-comp f g) x =
  cong (𝕀-Hom.map g) (𝕀-Hom.map-dec f x) ∙ 𝕀-Hom.map-dec g _

------------------------------------------------------------------------
-- Equality of morphisms
------------------------------------------------------------------------
-- Two 𝕀-Homs are equal iff their underlying maps are pointwise equal.
-- The remaining fields (map-cons, map-inc, map-dec) are equalities in
-- a set, hence propositions, so they are determined automatically.

𝕀-Hom-path : {A B : 𝕀-Alg} (f g : 𝕀-Hom A B)
           → (∀ a → 𝕀-Hom.map f a ≡ 𝕀-Hom.map g a)
           → f ≡ g
𝕀-Hom.map (𝕀-Hom-path f g h i) a = h a i
𝕀-Hom.map-cons (𝕀-Hom-path {A = A} {B = B} f g h i) d x =
  isProp→PathP (λ i → 𝕀-Alg.isSetCarrier B
    (h (𝕀-Alg.cons A d x) i) (𝕀-Alg.cons B d (h x i)))
    (𝕀-Hom.map-cons f d x) (𝕀-Hom.map-cons g d x) i
𝕀-Hom.map-inc (𝕀-Hom-path {A = A} {B = B} f g h i) x =
  isProp→PathP (λ i → 𝕀-Alg.isSetCarrier B
    (h (𝕀-Alg.inc A x) i) (𝕀-Alg.inc B (h x i)))
    (𝕀-Hom.map-inc f x) (𝕀-Hom.map-inc g x) i
𝕀-Hom.map-dec (𝕀-Hom-path {A = A} {B = B} f g h i) x =
  isProp→PathP (λ i → 𝕀-Alg.isSetCarrier B
    (h (𝕀-Alg.dec A x) i) (𝕀-Alg.dec B (h x i)))
    (𝕀-Hom.map-dec f x) (𝕀-Hom.map-dec g x) i
