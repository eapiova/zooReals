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

open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Sigma

open import Cubical.Data.Rationals.Fast as ℚ using (ℚ; [_/_])
open import Cubical.Data.Rationals.Fast.Properties as ℚP
  using (_+_; _-_; _·_; abs)
open import Cubical.Data.Rationals.Fast.Order as ℚO
  using (ℚ₊; _ℚ₊+_; 0<_; isTrans<; isTrans<≤; isTrans≤<; <Weaken≤
        ; <-o·; 0<→<; ·0<; absFrom<×<)
open import Cubical.Data.Rationals.Fast.Order.Properties as ℚOP
  using (/2₊; /3₊; /4₊; pos·abs)

open import Cubical.HITs.CauchyReals.Base
  using (ℝ; rat; lim; _∼[_]_; eqℝ; rat-rat-fromAbs; lim-lim; subst∼)
open import Cubical.HITs.CauchyReals.Closeness
  using (refl∼; sym∼; triangle∼; ∼→∼'; isSetℝ)
open import Cubical.HITs.CauchyReals.Lipschitz
  using (𝕣-lim-self; ∼-monotone≤)

open import Cubical.Codata.Stream.Properties using (Stream-η)

open import Reals.SignedDigit.Core
open import Reals.SignedDigit.Bounded
  using ( stream→ℝ; _≈sd_; 𝕀sd; [_]sd; isSet𝕀sd
        ; approx; approxℚ₊; approxℚ₊-cauchy; ℚ₊→ℕ; ℚ₊→ℕ-pred
        ; approx-unfold; approx-step; digitContrib; digitContrib-bound
        ; inv2^; modulus-correct; 0≤inv2^
        ; digitToℚ
        )
open import Reals.SignedDigit.IncDec
open import Reals.SignedDigit.HCIT.Algebra

open import Cubical.Tactics.CommRingSolverFast.FastRationalsReflection using (ℚ!!)

------------------------------------------------------------------------
-- cons on 𝕀sd
------------------------------------------------------------------------

-- Prepending a digit to a stream respects ≈sd:
-- if stream→ℝ s ≡ stream→ℝ t then stream→ℝ (d ∷ s) ≡ stream→ℝ (d ∷ t)
--
-- Proof strategy:
-- 1. Use eqℝ: show ∀ ε → stream→ℝ(d∷s) ∼[ε] stream→ℝ(d∷t)
-- 2. Use lim-lim to reduce to rational closeness
-- 3. By approx-unfold: approx(d∷s)(suc n) = digitContrib d 0 + (1/2)·approx s n
--    so the difference is (1/2)·(approx s n - approx t n)
-- 4. Bound |approx s n - approx t n| via a 5-step triangle chain through
--    the hypothesis stream→ℝ s ≡ stream→ℝ t

-- Helper: from a path in ℝ, extract closeness at every ε
≡→∼ : ∀ (x y : ℝ) → x ≡ y → ∀ ε → x ∼[ ε ] y
≡→∼ x y h ε = subst (x ∼[ ε ]_) h (refl∼ x ε)

-- Ring identity: (a+b·x)-(a+b·y) = b·(x-y) — proved with abstract variables
-- so the ring solver sees clean syntax
private
  cancel-ℚ : ∀ (a b x y : ℚ) →
    (a ℚP.+ b ℚP.· x) ℚP.- (a ℚP.+ b ℚP.· y)
    ≡ b ℚP.· (x ℚP.- y)
  cancel-ℚ a b x y = ℚ!!

cons-resp : (d : Digit) (s t : 𝟛ᴺ) → s ≈sd t → (d ∷ s) ≈sd (d ∷ t)
cons-resp d s t h = eqℝ _ _ close-all
  where
  -- From the hypothesis, get closeness at every ε
  h∼ : ∀ γ → stream→ℝ s ∼[ γ ] stream→ℝ t
  h∼ γ = ≡→∼ (stream→ℝ s) (stream→ℝ t) h γ

  close-all : ∀ ε → stream→ℝ (d ∷ s) ∼[ ε ] stream→ℝ (d ∷ t)
  close-all ε =
    lim-lim (λ δ → rat (approxℚ₊ (d ∷ s) δ))
            (λ δ → rat (approxℚ₊ (d ∷ t) δ))
            ε δ₀ δ₀
            (approxℚ₊-cauchy (d ∷ s))
            (approxℚ₊-cauchy (d ∷ t))
            v
            inner-close
    where
    -- δ₀ = ε/8 for lim-lim
    δ₀ : ℚ₊
    δ₀ = /4₊ (/2₊ ε)

    -- 3ε/4 = ε/2 + ε/4 as a convenient ℚ₊
    inner-tol : ℚ₊
    inner-tol = /2₊ ε ℚ₊+ /4₊ ε

    -- fst inner-tol ≡ fst ε - 2·fst δ₀  (ring identity: 3ε/4 = ε - ε/4)
    inner-eq : fst inner-tol ≡ fst ε ℚP.- (fst δ₀ ℚP.+ fst δ₀)
    inner-eq = ℚ!!

    -- Positivity: 0 < ε - 2δ₀ = 3ε/4 > 0
    v : 0< (fst ε ℚP.- (fst δ₀ ℚP.+ fst δ₀))
    v = subst (0<_) inner-eq (snd inner-tol)

    -- Abbreviations
    sf = λ δ → rat (approxℚ₊ s δ)
    sp = approxℚ₊-cauchy s
    tf = λ δ → rat (approxℚ₊ t δ)
    tp = approxℚ₊-cauchy t

    -- γ = ε/3 chosen so that (1/2)·(4δ₀ + 3γ) = inner-tol exactly
    γ : ℚ₊
    γ = /3₊ ε

    -- 𝕣-lim-self steps
    step2 : sf δ₀ ∼[ δ₀ ℚ₊+ γ ] stream→ℝ s
    step2 = 𝕣-lim-self sf sp δ₀ γ

    step4 : stream→ℝ t ∼[ δ₀ ℚ₊+ γ ] tf δ₀
    step4 = sym∼ (tf δ₀) (stream→ℝ t) (δ₀ ℚ₊+ γ)
              (𝕣-lim-self tf tp δ₀ γ)

    -- Predecessor of ℚ₊→ℕ δ₀ (suc m = ℚ₊→ℕ δ₀ definitionally)
    m : ℕ
    m = ℚ₊→ℕ-pred δ₀

    -- Cauchy bridge for s: |approx s (suc m) - approx s m| < fst δ₀
    bridge-s : rat (approx s (suc m)) ∼[ δ₀ ] rat (approx s m)
    bridge-s = rat-rat-fromAbs _ _ δ₀
      (isTrans≤< _ _ _
        (subst (ℚO._≤ inv2^ (suc m))
          (sym (cong abs (approx-step s m)))
          (digitContrib-bound (s ! suc m) (suc m)))
        (modulus-correct δ₀))

    -- Cauchy bridge for t
    bridge-t : rat (approx t (suc m)) ∼[ δ₀ ] rat (approx t m)
    bridge-t = rat-rat-fromAbs _ _ δ₀
      (isTrans≤< _ _ _
        (subst (ℚO._≤ inv2^ (suc m))
          (sym (cong abs (approx-step t m)))
          (digitContrib-bound (t ! suc m) (suc m)))
        (modulus-correct δ₀))

    -- 5-step triangle chain: rat(approx s m) ∼[chain-tol] rat(approx t m)
    -- Steps: sym(bridge-s) → step2 → h∼ γ → step4 → bridge-t
    chain-tol : ℚ₊
    chain-tol = (((δ₀ ℚ₊+ (δ₀ ℚ₊+ γ)) ℚ₊+ γ) ℚ₊+ (δ₀ ℚ₊+ γ)) ℚ₊+ δ₀

    chain : rat (approx s m) ∼[ chain-tol ] rat (approx t m)
    chain = triangle∼
      (triangle∼
        (triangle∼
          (triangle∼
            (sym∼ _ _ δ₀ bridge-s)
            step2)
          (h∼ γ))
        step4)
      bridge-t

    -- Extract two-sided bound via ∼→∼' (rat-rat case gives extractable pair)
    chain' : (ℚP.- fst chain-tol ℚO.< approx s m ℚP.- approx t m)
           × (approx s m ℚP.- approx t m ℚO.< fst chain-tol)
    chain' = ∼→∼' (rat (approx s m)) (rat (approx t m)) chain-tol chain

    -- abs bound on inner difference
    abs-diff : abs (approx s m ℚP.- approx t m) ℚO.< fst chain-tol
    abs-diff = absFrom<×< (fst chain-tol) (approx s m ℚP.- approx t m)
                 (fst chain') (snd chain')

    -- Difference identity via approx-unfold (split to help ring solver):
    -- Step 1: rewrite via approx-unfold
    diff-eq-a : approxℚ₊ (d ∷ s) δ₀ ℚP.- approxℚ₊ (d ∷ t) δ₀
              ≡ (digitContrib d zero ℚP.+ inv2^ zero ℚP.· approx s m)
                ℚP.- (digitContrib d zero ℚP.+ inv2^ zero ℚP.· approx t m)
    diff-eq-a = cong₂ ℚP._-_ (approx-unfold (d ∷ s) m) (approx-unfold (d ∷ t) m)

    -- Step 2: ring identity (a + b·x) - (a + b·y) = b·(x - y)
    diff-eq-b : (digitContrib d zero ℚP.+ inv2^ zero ℚP.· approx s m)
                ℚP.- (digitContrib d zero ℚP.+ inv2^ zero ℚP.· approx t m)
              ≡ inv2^ zero ℚP.· (approx s m ℚP.- approx t m)
    diff-eq-b = cancel-ℚ (digitContrib d zero) (inv2^ zero) (approx s m) (approx t m)

    diff-eq : approxℚ₊ (d ∷ s) δ₀ ℚP.- approxℚ₊ (d ∷ t) δ₀
            ≡ inv2^ zero ℚP.· (approx s m ℚP.- approx t m)
    diff-eq = diff-eq-a ∙ diff-eq-b

    -- Scale: abs(1/2 · x) = 1/2 · abs(x) < 1/2 · fst chain-tol
    abs-scaled : abs (inv2^ zero ℚP.· (approx s m ℚP.- approx t m))
               ℚO.< inv2^ zero ℚP.· fst chain-tol
    abs-scaled = subst (ℚO._< inv2^ zero ℚP.· fst chain-tol)
      (sym (pos·abs (inv2^ zero) (approx s m ℚP.- approx t m) (0≤inv2^ zero)))
      (<-o· (abs (approx s m ℚP.- approx t m)) (fst chain-tol)
            (inv2^ zero) (0<→< (inv2^ zero) ℚ.tt) abs-diff)

    -- Key identity: (1/2)·(4δ₀ + 3γ) = inner-tol  (exact with γ = ε/3)
    scale-eq : inv2^ zero ℚP.· fst chain-tol ≡ fst inner-tol
    scale-eq = ℚ!!

    -- Final abs bound
    abs-bound : abs (approxℚ₊ (d ∷ s) δ₀ ℚP.- approxℚ₊ (d ∷ t) δ₀) ℚO.< fst inner-tol
    abs-bound = subst2 (λ a b → abs a ℚO.< b) (sym diff-eq) scale-eq abs-scaled

    inner-close : rat (approxℚ₊ (d ∷ s) δ₀) ∼[ (fst ε ℚP.- (fst δ₀ ℚP.+ fst δ₀)) , v ] rat (approxℚ₊ (d ∷ t) δ₀)
    inner-close = subst∼ inner-eq
      (rat-rat-fromAbs (approxℚ₊ (d ∷ s) δ₀) (approxℚ₊ (d ∷ t) δ₀) inner-tol
        abs-bound)

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
-- Completeness and separation (postulated — requires inc-sem/dec-sem)
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
