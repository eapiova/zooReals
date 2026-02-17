{-# OPTIONS --cubical --guardedness #-}

------------------------------------------------------------------------
-- 𝕀sd as an 𝕀-Algebra
------------------------------------------------------------------------
--
-- We show that the quotient 𝕀sd = 𝟛ᴺ / _≈sd_ carries an 𝕀-Algebra
-- structure using:
--   • cons𝕀 from the quotient-lifted stream cons
--   • inc𝕀, dec𝕀 from IncDec.agda
--   • equations proved semantically (both sides have the same image
--     under ι : 𝕀sd → ℝ, so they're equal by the quotient structure)

module Reals.SignedDigit.HCIT.Structure where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.HITs.SetQuotients as SQ
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁; ∣_∣₁)

open import Cubical.Data.Sigma

open import Cubical.Codata.Stream.Properties using (Stream-η)

open import Reals.SignedDigit.Core
open import Reals.SignedDigit.Bounded
  using ( stream→ℝ; _≈sd_; 𝕀sd; [_]sd; isSet𝕀sd )
open import Reals.SignedDigit.ConsResp using (cons-resp)
open import Reals.SignedDigit.IncDec
open import Reals.SignedDigit.HCIT.Algebra

------------------------------------------------------------------------
-- cons on 𝕀sd
------------------------------------------------------------------------
-- cons-resp (prepending preserves ≈sd) is proved in ConsResp.agda.
-- Here we lift it to the quotient.

cons𝕀 : Digit → 𝕀sd → 𝕀sd
cons𝕀 d = SQ.rec isSet𝕀sd (λ s → [ d ∷ s ]sd)
  (λ s t h → eq/ (d ∷ s) (d ∷ t) (cons-resp d s t h))

------------------------------------------------------------------------
-- inc/dec equations on 𝕀sd
------------------------------------------------------------------------
-- Each equation holds because both sides are definitionally equal at
-- the head/tail level on raw streams. Stream-η gives the path in 𝟛ᴺ,
-- cong stream→ℝ gives ≈sd, and eq/ gives the quotient path.

-- inc equations (slide 13)
inc⁻¹-𝕀 : ∀ (x : 𝕀sd) → inc𝕀 (cons𝕀 -1d x) ≡ cons𝕀 0d (inc𝕀 x)
inc⁻¹-𝕀 = SQ.elimProp (λ _ → isSet𝕀sd _ _) λ s →
  eq/ (inc-aux -1d s) (0d ∷ inc s)
      (cong stream→ℝ (Stream-η {xs = inc-aux -1d s}))

inc⁰-𝕀 : ∀ (x : 𝕀sd) → inc𝕀 (cons𝕀 0d x) ≡ cons𝕀 +1d (cons𝕀  0d x)
inc⁰-𝕀 = SQ.elimProp (λ _ → isSet𝕀sd _ _) λ s →
  eq/ (inc-aux 0d s) (+1d ∷ (0d ∷ s))
      (cong stream→ℝ (Stream-η {xs = inc-aux 0d s}))

inc⁺¹-𝕀 : ∀ (x : 𝕀sd) → inc𝕀 (cons𝕀 +1d x) ≡ cons𝕀 +1d (inc𝕀 x)
inc⁺¹-𝕀 = SQ.elimProp (λ _ → isSet𝕀sd _ _) λ s →
  eq/ (inc-aux +1d s) (+1d ∷ inc s)
      (cong stream→ℝ (Stream-η {xs = inc-aux +1d s}))

-- dec equations (slide 13)
dec⁺¹-𝕀 : ∀ (x : 𝕀sd) → dec𝕀 (cons𝕀 +1d x) ≡ cons𝕀 0d (dec𝕀 x)
dec⁺¹-𝕀 = SQ.elimProp (λ _ → isSet𝕀sd _ _) λ s →
  eq/ (dec-aux +1d s) (0d ∷ dec s)
      (cong stream→ℝ (Stream-η {xs = dec-aux +1d s}))

dec⁰-𝕀 : ∀ (x : 𝕀sd) → dec𝕀 (cons𝕀 0d x) ≡ cons𝕀 -1d (cons𝕀 0d x)
dec⁰-𝕀 = SQ.elimProp (λ _ → isSet𝕀sd _ _) λ s →
  eq/ (dec-aux 0d s) (-1d ∷ (0d ∷ s))
      (cong stream→ℝ (Stream-η {xs = dec-aux 0d s}))

dec⁻¹-𝕀 : ∀ (x : 𝕀sd) → dec𝕀 (cons𝕀 -1d x) ≡ cons𝕀 -1d (dec𝕀 x)
dec⁻¹-𝕀 = SQ.elimProp (λ _ → isSet𝕀sd _ _) λ s →
  eq/ (dec-aux -1d s) (-1d ∷ dec s)
      (cong stream→ℝ (Stream-η {xs = dec-aux -1d s}))

------------------------------------------------------------------------
-- Completeness and separation (postulated — semantic arithmetic)
------------------------------------------------------------------------

postulate
  -- Completeness (slide 14)
  carry-compl-𝕀  : ∀ x y → cons𝕀 0d x ≡ inc𝕀 y → cons𝕀 -1d x ≡ cons𝕀 0d y
  borrow-compl-𝕀 : ∀ x y → cons𝕀 0d x ≡ dec𝕀 y → cons𝕀 +1d x ≡ cons𝕀 0d y

  -- Separation (slide 18)
  sep-L-𝕀 : ∀ x y → cons𝕀 -1d x ≡ cons𝕀 0d y → cons𝕀 0d x ≡ inc𝕀 y
  sep-R-𝕀 : ∀ x y → cons𝕀 +1d x ≡ cons𝕀 0d y → cons𝕀 0d x ≡ dec𝕀 y

------------------------------------------------------------------------
-- Generation
------------------------------------------------------------------------

-- Every element of 𝕀sd is of the form cons𝕀 d x for some d and x.
-- Proof: eliminate on the quotient. For [s]sd, the witness is
-- (head s, [tail s]sd).

gen-𝕀 : ∀ (y : 𝕀sd) → ∥ Σ[ d ∈ Digit ] Σ[ x ∈ 𝕀sd ] (y ≡ cons𝕀 d x) ∥₁
gen-𝕀 = SQ.elimProp (λ _ → squash₁) go
  where
  squash₁ = Cubical.HITs.PropositionalTruncation.isPropPropTrunc

  -- For a raw stream s, decompose as (head s) ∷ (tail s)
  -- and show [s]sd ≡ cons𝕀 (head s) [tail s]sd
  go : (s : 𝟛ᴺ) → ∥ Σ[ d ∈ Digit ] Σ[ x ∈ 𝕀sd ] ([ s ]sd ≡ cons𝕀 d x) ∥₁
  go s = ∣ head s , [ tail s ]sd , eq/ s (head s ∷ tail s) stream-eq ∣₁
    where
    -- s ≡ head s ∷ tail s by stream η, hence ≈sd (same image under stream→ℝ)
    stream-eq : s ≈sd (head s ∷ tail s)
    stream-eq = cong stream→ℝ (Stream-η {xs = s})

------------------------------------------------------------------------
-- Carry/borrow on 𝕀sd (constructive from raw carry/borrow)
------------------------------------------------------------------------

carry-𝕀 : ∀ (x : 𝕀sd) → cons𝕀 +1d (cons𝕀 -1d x) ≡ cons𝕀 0d (inc𝕀 x)
carry-𝕀 = SQ.elimProp (λ _ → isSet𝕀sd _ _) (λ s → carry𝕀 s)

borrow-𝕀 : ∀ (x : 𝕀sd) → cons𝕀 -1d (cons𝕀 +1d x) ≡ cons𝕀 0d (dec𝕀 x)
borrow-𝕀 = SQ.elimProp (λ _ → isSet𝕀sd _ _) (λ s → borrow𝕀 s)

------------------------------------------------------------------------
-- 𝕀sd as an 𝕀-Algebra
------------------------------------------------------------------------

𝕀sd-Alg : 𝕀-Alg
𝕀-Alg.Carrier      𝕀sd-Alg = 𝕀sd
𝕀-Alg.isSetCarrier 𝕀sd-Alg = isSet𝕀sd
𝕀-Alg.cons         𝕀sd-Alg = cons𝕀
𝕀-Alg.inc          𝕀sd-Alg = inc𝕀
𝕀-Alg.dec          𝕀sd-Alg = dec𝕀
𝕀-Alg.inc⁻¹        𝕀sd-Alg = inc⁻¹-𝕀
𝕀-Alg.inc⁰         𝕀sd-Alg = inc⁰-𝕀
𝕀-Alg.inc⁺¹        𝕀sd-Alg = inc⁺¹-𝕀
𝕀-Alg.dec⁺¹        𝕀sd-Alg = dec⁺¹-𝕀
𝕀-Alg.dec⁰         𝕀sd-Alg = dec⁰-𝕀
𝕀-Alg.dec⁻¹        𝕀sd-Alg = dec⁻¹-𝕀
𝕀-Alg.carry        𝕀sd-Alg = carry-𝕀
𝕀-Alg.borrow       𝕀sd-Alg = borrow-𝕀
𝕀-Alg.gen          𝕀sd-Alg = gen-𝕀
𝕀-Alg.carry-compl  𝕀sd-Alg = carry-compl-𝕀
𝕀-Alg.borrow-compl 𝕀sd-Alg = borrow-compl-𝕀
𝕀-Alg.sep-L        𝕀sd-Alg = sep-L-𝕀
𝕀-Alg.sep-R        𝕀sd-Alg = sep-R-𝕀
