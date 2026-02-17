{-# OPTIONS --cubical --guardedness #-}

------------------------------------------------------------------------
-- cons-resp: Prepending a digit respects ≈sd
------------------------------------------------------------------------
--
-- Extracted from HCIT/Structure.agda to break a module dependency cycle:
-- IncDec.agda needs cons-resp to prove inc-resp/dec-resp, but
-- Structure.agda imports IncDec.agda. This module sits between
-- Bounded.agda and IncDec.agda in the dependency graph.

module Reals.SignedDigit.ConsResp where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Sigma using (_×_)

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

open import Reals.SignedDigit.Core
open import Reals.SignedDigit.Bounded
  using ( stream→ℝ; _≈sd_; 𝕀sd; [_]sd; isSet𝕀sd
        ; approx; approxℚ₊; approxℚ₊-cauchy; ℚ₊→ℕ; ℚ₊→ℕ-pred
        ; approx-unfold; approx-step; digitContrib; digitContrib-bound
        ; inv2^; modulus-correct; 0≤inv2^
        ; digitToℚ
        )

open import Cubical.Tactics.CommRingSolverFast.FastRationalsReflection using (ℚ!!)

------------------------------------------------------------------------
-- Helper: from a path in ℝ, extract closeness at every ε
------------------------------------------------------------------------

≡→∼ : ∀ (x y : ℝ) → x ≡ y → ∀ ε → x ∼[ ε ] y
≡→∼ x y h ε = subst (x ∼[ ε ]_) h (refl∼ x ε)

------------------------------------------------------------------------
-- Ring identity: (a+b·x)-(a+b·y) = b·(x-y)
------------------------------------------------------------------------

private
  cancel-ℚ : ∀ (a b x y : ℚ) →
    (a ℚP.+ b ℚP.· x) ℚP.- (a ℚP.+ b ℚP.· y)
    ≡ b ℚP.· (x ℚP.- y)
  cancel-ℚ a b x y = ℚ!!

------------------------------------------------------------------------
-- cons-resp: prepending a digit preserves ≈sd
------------------------------------------------------------------------

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
