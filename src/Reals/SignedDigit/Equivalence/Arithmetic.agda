{-# OPTIONS --cubical #-}

------------------------------------------------------------------------
-- Arithmetic Lemmas for Signed-Digit Equivalence
------------------------------------------------------------------------
--
-- This module contains pure ℚ arithmetic lemmas used in the Direct
-- approach. Separated for faster compilation (these proofs are slow
-- due to path algebra over rationals).
--
------------------------------------------------------------------------

module Reals.SignedDigit.Equivalence.Arithmetic where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Int as ℤ using (ℤ; pos)
open import Cubical.Data.Rationals.Fast as ℚ
open import Cubical.Data.Rationals.Fast.Properties as ℚP
open import Cubical.Data.Rationals.Fast.Order as ℚO
  using (ℚ₊; ℚ₊≡)
open import Cubical.Data.Rationals.Fast.Order.Properties as ℚOP
  using (/2₊; ε/2+ε/2≡ε)

-- Alias for ℚ₊ addition
_+₊_ : ℚ₊ → ℚ₊ → ℚ₊
_+₊_ = ℚO._ℚ₊+_

------------------------------------------------------------------------
-- Half operations
------------------------------------------------------------------------

-- Helper: ε/2 + ε/2 ≡ ε (as ℚ₊)
/2₊+/2₊≡ε₊ : ∀ ε → /2₊ ε +₊ /2₊ ε ≡ ε
/2₊+/2₊≡ε₊ ε = ℚO.ℚ₊≡ (ε/2+ε/2≡ε (fst ε))

-- Helper: (δ + ε)/2 = δ/2 + ε/2 (distributivity of /2₊ over +₊)
-- Proof: (δ + ε) · 1/2 = δ · 1/2 + ε · 1/2 by ·DistR+
/2₊-dist : ∀ δ ε → /2₊ (δ +₊ ε) ≡ /2₊ δ +₊ /2₊ ε
/2₊-dist δ ε = ℚO.ℚ₊≡ eq
  where
    open import Cubical.Data.Rationals.Fast.Base as ℚB using ([_/_])
    open import Cubical.Data.NatPlusOne using (1+_)
    half : ℚ.ℚ
    half = ℚB.[_/_] (pos 1) (1+ 1)  -- 1/2 where denominator is ℕ₊₁
    eq : fst (/2₊ (δ +₊ ε)) ≡ fst (/2₊ δ +₊ /2₊ ε)
    eq = ℚP.·DistR+ (fst δ) (fst ε) half

------------------------------------------------------------------------
-- Basic arithmetic identities
------------------------------------------------------------------------

-- Key lemma: (x - y) + y ≡ x
-- Proof: (x + (-y)) + y = x + ((-y) + y) = x + 0 = x
x-y+y≡x : ∀ x y → (x ℚP.- y) ℚ.+ y ≡ x
x-y+y≡x x y = sym (ℚP.+Assoc x (ℚP.- y) y) ∙ cong (x ℚ.+_) (ℚP.+InvL y) ∙ ℚP.+IdR x

-- Helper: (-a) + (b + a) ≡ b
-- Proof: (-a) + (b + a) = (-a) + (a + b) = ((-a) + a) + b = 0 + b = b
-a+[b+a]≡b : ∀ a b → (ℚP.- a) ℚ.+ (b ℚ.+ a) ≡ b
-a+[b+a]≡b a b =
  cong ((ℚP.- a) ℚ.+_) (ℚP.+Comm b a)
  ∙ ℚP.+Assoc (ℚP.- a) a b
  ∙ cong (ℚ._+ b) (ℚP.+InvL a)
  ∙ ℚP.+IdL b

-- Helper: x - (y + z) ≡ (x - y) - z
-- Proof: x - (y + z) = x + (-(y + z)) = x + ((-y) + (-z)) = (x + (-y)) + (-z) = (x - y) - z
x-[y+z]≡x-y-z : ∀ x y z → x ℚP.- (y ℚ.+ z) ≡ (x ℚP.- y) ℚP.- z
x-[y+z]≡x-y-z x y z =
  cong (x ℚ.+_) (ℚP.-Distr y z)  -- x + (-(y+z)) = x + ((-y) + (-z))
  ∙ ℚP.+Assoc x (ℚP.- y) (ℚP.- z)  -- = (x + (-y)) + (-z) = (x - y) - z

------------------------------------------------------------------------
-- Bound equations for coherence proofs
------------------------------------------------------------------------

-- Main bound equation: 2(e - d) + 2d = 2e
-- i.e., ((e - d) + (e - d)) + (d + d) ≡ (e + e)
bound-2[e-d]+2d≡2e : ∀ e d → ((e ℚP.- d) ℚ.+ (e ℚP.- d)) ℚ.+ (d ℚ.+ d) ≡ e ℚ.+ e
bound-2[e-d]+2d≡2e e d =
  -- Step 1: ((e-d) + (e-d)) + (d+d) = (e-d) + ((e-d) + (d+d))
  sym (ℚP.+Assoc (e ℚP.- d) (e ℚP.- d) (d ℚ.+ d))
  -- Step 2: (e-d) + (d+d) = ((e-d) + d) + d = e + d
  ∙ cong ((e ℚP.- d) ℚ.+_) (ℚP.+Assoc (e ℚP.- d) d d ∙ cong (ℚ._+ d) (x-y+y≡x e d))
  -- Now we have: (e-d) + (e + d) = (e + (-d)) + (e + d)
  -- Step 3: e + ((-d) + (e + d)) by sym +Assoc
  ∙ sym (ℚP.+Assoc e (ℚP.- d) (e ℚ.+ d))
  -- Step 4: (-d) + (e + d) = e by -a+[b+a]≡b
  ∙ cong (e ℚ.+_) (-a+[b+a]≡b d e)

-- Triple bound equation: 2δ + 2(ε - δ - η) + 2η = 2ε
-- i.e., ((d + d) + ((e - d - h) + (e - d - h))) + (h + h) ≡ e + e
-- Proof: Follows from δ + (ε - δ - η) + η = ε, then "doubled"
bound-2d+2[e-d-h]+2h≡2e : ∀ e d h → (((d ℚ.+ d) ℚ.+ (((e ℚP.- d) ℚP.- h) ℚ.+ ((e ℚP.- d) ℚP.- h))) ℚ.+ (h ℚ.+ h)) ≡ e ℚ.+ e
bound-2d+2[e-d-h]+2h≡2e e d h =
  -- The key insight: (e - d - h) = (e - d) - h, so:
  -- d + ((e - d) - h) + h = d + (e - d) = e (using x-y+y≡x twice)
  -- Then the 2x version follows by the same algebraic manipulations.
  let
    edh = (e ℚP.- d) ℚP.- h  -- e - d - h = (e - d) - h
    ed = e ℚP.- d          -- e - d

    -- First, we simplify using the structure: 2d + 2(ed - h) + 2h
    -- We use: 2(ed - h) + 2h = 2ed (by bound-2[e-d]+2d≡2e with ed and h)
    step1 : ((edh ℚ.+ edh) ℚ.+ (h ℚ.+ h)) ≡ ed ℚ.+ ed
    step1 = bound-2[e-d]+2d≡2e ed h

    -- Then: 2d + 2ed = 2e (by commutativity and bound-2[e-d]+2d≡2e with e and d)
    step2 : (d ℚ.+ d) ℚ.+ (ed ℚ.+ ed) ≡ e ℚ.+ e
    step2 = ℚP.+Comm (d ℚ.+ d) (ed ℚ.+ ed) ∙ bound-2[e-d]+2d≡2e e d

    -- Combine: ((2d + 2edh) + 2h) = 2d + (2edh + 2h) = 2d + 2ed = 2e
  in sym (ℚP.+Assoc (d ℚ.+ d) (edh ℚ.+ edh) (h ℚ.+ h))
     ∙ cong ((d ℚ.+ d) ℚ.+_) step1
     ∙ step2
