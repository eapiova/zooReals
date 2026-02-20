{-# OPTIONS --cubical #-}

------------------------------------------------------------------------
-- Comparison: PointedMidpointAlg → 𝕀-Alg equations
------------------------------------------------------------------------
--
-- Given a PointedMidpointAlg P, we derive 𝕀-Alg operations:
--   cons d x = digitPoint d ⊕ x
--   inc x    = top ⊕ x
--   dec x    = bot ⊕ x
--
-- and prove 8 of the 13 𝕀-Alg equations purely from the midpoint
-- axioms (idempotency, commutativity, mediality). No postulates.
--
-- The remaining 5 equations (gen, carry-compl, borrow-compl, sep-L,
-- sep-R) require additional structure (iteration + cancellation)
-- and are passed as explicit arguments when constructing a full 𝕀-Alg.

module Reals.SignedDigit.Midpoint.Comparison where

open import Cubical.Foundations.Prelude
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁)
open import Cubical.Data.Sigma

open import Reals.SignedDigit.Core using (Digit; -1d; 0d; +1d)
open import Reals.SignedDigit.Midpoint.Algebra
open import Reals.SignedDigit.HCIT.Algebra

------------------------------------------------------------------------
-- Derived operations and equations
------------------------------------------------------------------------

module Core (P : PointedMidpointAlg) where
  open PointedMidpointAlg P

  -- Derived 𝕀-Alg operations
  cons-M : Digit → Carrier → Carrier
  cons-M d x = digitPoint d ⊕ x

  inc-M : Carrier → Carrier
  inc-M x = top ⊕ x

  dec-M : Carrier → Carrier
  dec-M x = bot ⊕ x

  ----------------------------------------------------------------------
  -- Helper lemma: idempotent distribution
  -- From idem + medial: a ⊕ (b ⊕ c) = (a ⊕ b) ⊕ (a ⊕ c)
  ----------------------------------------------------------------------

  idem-distrib : ∀ a b c → a ⊕ (b ⊕ c) ≡ (a ⊕ b) ⊕ (a ⊕ c)
  idem-distrib a b c =
    sym (cong (_⊕ (b ⊕ c)) (idem a)) ∙ medial a a b c

  ----------------------------------------------------------------------
  -- The 8 provable equations
  ----------------------------------------------------------------------

  -- inc (cons -1 x) ≡ cons 0 (inc x)
  -- i.e., top ⊕ (bot ⊕ x) ≡ (bot ⊕ top) ⊕ (top ⊕ x)
  --
  -- Proof: top ⊕ (bot ⊕ x)
  --      = (top ⊕ top) ⊕ (bot ⊕ x)    [idem top]
  --      = (top ⊕ bot) ⊕ (top ⊕ x)    [medial]
  --      = (bot ⊕ top) ⊕ (top ⊕ x)    [comm on first factor]
  inc⁻¹-M : ∀ x → inc-M (cons-M -1d x) ≡ cons-M 0d (inc-M x)
  inc⁻¹-M x =
    idem-distrib top bot x
    ∙ cong (_⊕ (top ⊕ x)) (comm top bot)

  -- inc (cons 0 x) ≡ cons +1 (cons 0 x)
  -- i.e., top ⊕ ((bot ⊕ top) ⊕ x) ≡ top ⊕ ((bot ⊕ top) ⊕ x)
  inc⁰-M : ∀ x → inc-M (cons-M 0d x) ≡ cons-M +1d (cons-M 0d x)
  inc⁰-M x = refl

  -- inc (cons +1 x) ≡ cons +1 (inc x)
  -- i.e., top ⊕ (top ⊕ x) ≡ top ⊕ (top ⊕ x)
  inc⁺¹-M : ∀ x → inc-M (cons-M +1d x) ≡ cons-M +1d (inc-M x)
  inc⁺¹-M x = refl

  -- dec (cons +1 x) ≡ cons 0 (dec x)
  -- i.e., bot ⊕ (top ⊕ x) ≡ (bot ⊕ top) ⊕ (bot ⊕ x)
  dec⁺¹-M : ∀ x → dec-M (cons-M +1d x) ≡ cons-M 0d (dec-M x)
  dec⁺¹-M x = idem-distrib bot top x

  -- dec (cons 0 x) ≡ cons -1 (cons 0 x)
  -- i.e., bot ⊕ ((bot ⊕ top) ⊕ x) ≡ bot ⊕ ((bot ⊕ top) ⊕ x)
  dec⁰-M : ∀ x → dec-M (cons-M 0d x) ≡ cons-M -1d (cons-M 0d x)
  dec⁰-M x = refl

  -- dec (cons -1 x) ≡ cons -1 (dec x)
  -- i.e., bot ⊕ (bot ⊕ x) ≡ bot ⊕ (bot ⊕ x)
  dec⁻¹-M : ∀ x → dec-M (cons-M -1d x) ≡ cons-M -1d (dec-M x)
  dec⁻¹-M x = refl

  -- carry: cons +1 (cons -1 x) ≡ cons 0 (inc x)
  -- Same statement as inc⁻¹-M
  carry-M : ∀ x → cons-M +1d (cons-M -1d x) ≡ cons-M 0d (inc-M x)
  carry-M = inc⁻¹-M

  -- borrow: cons -1 (cons +1 x) ≡ cons 0 (dec x)
  -- Same statement as dec⁺¹-M
  borrow-M : ∀ x → cons-M -1d (cons-M +1d x) ≡ cons-M 0d (dec-M x)
  borrow-M = dec⁺¹-M

------------------------------------------------------------------------
-- Full 𝕀-Alg packaging (8 derived + 5 supplied)
------------------------------------------------------------------------

record RemainingAxioms (P : PointedMidpointAlg) : Type₁ where
  open PointedMidpointAlg P
  module C = Core P

  field
    gen : ∀ y → ∥ Σ[ d ∈ Digit ] Σ[ x ∈ Carrier ] (y ≡ C.cons-M d x) ∥₁

    carry-compl : ∀ x y
      → C.cons-M 0d x ≡ C.inc-M y
      → C.cons-M -1d x ≡ C.cons-M 0d y

    borrow-compl : ∀ x y
      → C.cons-M 0d x ≡ C.dec-M y
      → C.cons-M +1d x ≡ C.cons-M 0d y

    sep-L : ∀ x y
      → C.cons-M -1d x ≡ C.cons-M 0d y
      → C.cons-M 0d x ≡ C.inc-M y

    sep-R : ∀ x y
      → C.cons-M +1d x ≡ C.cons-M 0d y
      → C.cons-M 0d x ≡ C.dec-M y

build𝕀-Alg : (P : PointedMidpointAlg) → RemainingAxioms P → 𝕀-Alg
build𝕀-Alg P R = A
  where
  module P = PointedMidpointAlg P
  module C = Core P
  module R = RemainingAxioms R

  A : 𝕀-Alg
  𝕀-Alg.Carrier A = P.Carrier
  𝕀-Alg.isSetCarrier A = P.isSetCarrier
  𝕀-Alg.cons A = C.cons-M
  𝕀-Alg.inc A = C.inc-M
  𝕀-Alg.dec A = C.dec-M
  𝕀-Alg.inc⁻¹ A = C.inc⁻¹-M
  𝕀-Alg.inc⁰ A = C.inc⁰-M
  𝕀-Alg.inc⁺¹ A = C.inc⁺¹-M
  𝕀-Alg.dec⁺¹ A = C.dec⁺¹-M
  𝕀-Alg.dec⁰ A = C.dec⁰-M
  𝕀-Alg.dec⁻¹ A = C.dec⁻¹-M
  𝕀-Alg.carry A = C.carry-M
  𝕀-Alg.borrow A = C.borrow-M
  𝕀-Alg.gen A = R.gen
  𝕀-Alg.carry-compl A = R.carry-compl
  𝕀-Alg.borrow-compl A = R.borrow-compl
  𝕀-Alg.sep-L A = R.sep-L
  𝕀-Alg.sep-R A = R.sep-R
