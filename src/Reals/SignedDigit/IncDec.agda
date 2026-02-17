{-# OPTIONS --cubical --guardedness #-}

------------------------------------------------------------------------
-- Carry-increment and borrow-decrement on signed-digit streams
------------------------------------------------------------------------
--
-- Following Altenkirch, "The Reals as a Higher Coinductive Type?"
-- (slides 12–13):
--
--   Semantics:  ⟦inc(s)⟧ = 1/2 + ⟦s⟧/2    (affine shift up)
--               ⟦dec(s)⟧ = -1/2 + ⟦s⟧/2   (affine shift down)
--
-- These are NOT inverses: inc ∘ dec ≠ id, dec ∘ inc ≠ id.
--
-- Defining equations (corecursive on streams):
--   inc (-1 ∷ x) = 0  ∷ inc x       (carry propagates)
--   inc ( 0 ∷ x) = +1 ∷ (0 ∷ x)    (carry absorbed)
--   inc (+1 ∷ x) = +1 ∷ inc x       (carry propagates)
--
--   dec (+1 ∷ x) = 0  ∷ dec x       (borrow propagates)
--   dec ( 0 ∷ x) = -1 ∷ (0 ∷ x)    (borrow absorbed)
--   dec (-1 ∷ x) = -1 ∷ dec x       (borrow propagates)

module Reals.SignedDigit.IncDec where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat using (ℕ; zero; suc)

open import Cubical.Codata.Stream as StreamM using (Stream; _,_)
open StreamM.Stream
open import Cubical.Codata.Stream.Properties using (Stream-η)

open import Cubical.HITs.SetQuotients as SQ

open import Cubical.Data.Rationals.Fast as ℚ using (ℚ)
open import Cubical.Data.Rationals.Fast.Properties as ℚP
  using (_+_; _-_; _·_; abs; ·Comm)
open import Cubical.Data.Rationals.Fast.Order as ℚO
  using ( ℚ₊; _ℚ₊+_; 0<_; isTrans<; isTrans≤<; isTrans≤
        ; <Weaken≤; absFrom≤×≤; ≤-·o; isRefl≤)
open import Cubical.Data.Rationals.Fast.Order.Properties as ℚOP
  using (/2₊; /3₊; /4₊; pos·abs)

open import Cubical.HITs.CauchyReals.Base
  using (ℝ; rat; lim; eqℝ; _∼[_]_; rat-rat-fromAbs; lim-lim; subst∼)
open import Cubical.HITs.CauchyReals.Closeness using (isSetℝ; refl∼)

open import Cubical.Tactics.CommRingSolverFast.FastRationalsReflection using (ℚ!!)

open import Reals.SignedDigit.Core
open import Reals.SignedDigit.Bounded
  using ( stream→ℝ; _≈sd_; 𝕀sd; [_]sd; isSet𝕀sd
        ; stream→ℝ-resp; ι
        ; approx; approxℚ₊; approxℚ₊-cauchy; ℚ₊→ℕ
        ; approx-unfold
        ; digitContrib; digitToℚ; inv2^; modulus-correct; 0≤inv2^
        ; half-inv2^; inv2^-double
        ; 0ℚ; 1ℚ; -1ℚ
        ; ·ZeroL; ·OneL; ·NegOneL
        ; abs-0ℚ; abs-neg; abs-pos-inv2^
        )
open import Reals.SignedDigit.ConsResp using (cons-resp)

------------------------------------------------------------------------
-- inc: tail-carry increment
------------------------------------------------------------------------

-- Helper that takes the head digit explicitly, avoiding with-clause
-- guardedness issues. The -1d and +1d cases are guarded (corecursive
-- call under tail). The 0d case is non-recursive.

inc-aux : Digit → 𝟛ᴺ → 𝟛ᴺ

head (inc-aux -1d x) = 0d
tail (inc-aux -1d x) = inc-aux (head x) (tail x)

head (inc-aux 0d x) = +1d
tail (inc-aux 0d x) = 0d ∷ x

head (inc-aux +1d x) = +1d
tail (inc-aux +1d x) = inc-aux (head x) (tail x)

inc : 𝟛ᴺ → 𝟛ᴺ
inc s = inc-aux (head s) (tail s)

------------------------------------------------------------------------
-- dec: tail-borrow decrement
------------------------------------------------------------------------

dec-aux : Digit → 𝟛ᴺ → 𝟛ᴺ

head (dec-aux +1d x) = 0d
tail (dec-aux +1d x) = dec-aux (head x) (tail x)

head (dec-aux 0d x) = -1d
tail (dec-aux 0d x) = 0d ∷ x

head (dec-aux -1d x) = -1d
tail (dec-aux -1d x) = dec-aux (head x) (tail x)

dec : 𝟛ᴺ → 𝟛ᴺ
dec s = dec-aux (head s) (tail s)

------------------------------------------------------------------------
-- Semantic correctness: stream→ℝ (inc s) ≡ stream→ℝ (+1d ∷ s)
------------------------------------------------------------------------
--
-- Key insight: inc-aux d x has the same Cauchy-real limit as +1d ∷ (d ∷ x).
-- Proved via eqℝ + lim-lim, using a bound on rational approximants.
--
-- The core bound (inc-aux-bound) is by ℕ-induction on n, case-splitting
-- on d. The -1d case uses the algebraic cancellation:
--   digitContrib 0d 0 - digitContrib +1d 0 + inv2^0 · (B - C) = 0
-- where B - C = approx(+1d ∷ x)(n) - approx(-1d ∷ x)(n) = 2·inv2^0.

------------------------------------------------------------------------
-- Helper lemmas for rational arithmetic
------------------------------------------------------------------------

private
  -- Ring identity: (a + h·A) - (b + h·C) = (a - b) + h·(A - C)
  cancel-ab : ∀ (a b h A C : ℚ) →
    (a ℚP.+ h ℚP.· A) ℚP.- (b ℚP.+ h ℚP.· C)
    ≡ (a ℚP.- b) ℚP.+ h ℚP.· (A ℚP.- C)
  cancel-ab a b h A C = ℚ!!

  -- Ring identity: (-h) + h·(x + 1) = h·x  (uses 1 as ring unit)
  neg-cancel : ∀ (h x : ℚ) →
    (ℚP.- h) ℚP.+ h ℚP.· (x ℚP.+ 1ℚ) ≡ h ℚP.· x
  neg-cancel h x = ℚ!!

  -- Ring identity: h + h·(x + (-1)) = h·x
  pos-cancel : ∀ (h x : ℚ) →
    h ℚP.+ h ℚP.· (x ℚP.+ (ℚP.- 1ℚ)) ≡ h ℚP.· x
  pos-cancel h x = ℚ!!

  -- Ring identity: x - y = -(y - x)
  minus-flip : ∀ (x y : ℚ) → x ℚP.- y ≡ ℚP.- (y ℚP.- x)
  minus-flip x y = ℚ!!

  -- 0 - x = -x
  zero-minus : ∀ (x : ℚ) → 0ℚ ℚP.- x ≡ ℚP.- x
  zero-minus x = ℚ!!

  -- x - x = 0
  self-minus : ∀ (x : ℚ) → x ℚP.- x ≡ 0ℚ
  self-minus x = ℚ!!

  -- Scale IH: from |t| ≤ inv2^n derive inv2^0 · |t| ≤ inv2^(suc n)
  scale-bound : ∀ (t : ℚ) (n : ℕ) → abs t ℚO.≤ inv2^ n →
                inv2^ zero ℚP.· abs t ℚO.≤ inv2^ (suc n)
  scale-bound t n p =
    subst2 ℚO._≤_
      (ℚP.·Comm (abs t) (inv2^ zero))
      (ℚP.·Comm (inv2^ n) (inv2^ zero) ∙ half-inv2^ n)
      (≤-·o (abs t) (inv2^ n) (inv2^ zero) (0≤inv2^ zero) p)

------------------------------------------------------------------------
-- Digit contribution equalities
------------------------------------------------------------------------

private
  dC0≡0 : digitContrib 0d zero ≡ 0ℚ
  dC0≡0 = ·ZeroL (inv2^ zero)

  dCp≡h : digitContrib +1d zero ≡ inv2^ zero
  dCp≡h = ·OneL (inv2^ zero)

  dCm≡-h : digitContrib -1d zero ≡ ℚP.- inv2^ zero
  dCm≡-h = ·NegOneL (inv2^ zero)

  -- inv2^0 + inv2^0 = 1ℚ
  -- Proof: inv2^-double 0 gives inv2^0 ≡ inv2^1 + inv2^1,
  -- so inv2^0 + inv2^0 = (inv2^1 + inv2^1) + (inv2^1 + inv2^1)
  -- Actually simpler: 2·inv2^-suc gives 2·inv2^1 = inv2^0,
  -- and x+x = 2·x, so inv2^0 + inv2^0 = 2·inv2^0.
  -- But we need 2·inv2^0 = 1. Let me use ℚ!! after reducing to known forms.
  -- Actually, inv2^0 = [1/2], so [1/2]+[1/2] = [1/1] = 1ℚ, which ℚ!! handles.
  two-h-is-one : inv2^ zero ℚP.+ inv2^ zero ≡ 1ℚ
  two-h-is-one = ℚ!!

------------------------------------------------------------------------
-- Prefix difference: approx(+1d ∷ x)(n) - approx(-1d ∷ x)(n) = 2·inv2^0
------------------------------------------------------------------------
-- The two streams share their tail; only the first digit differs.
-- By approx-unfold, the tail contribution cancels.

private
  prefix-diff-zero : (x : 𝟛ᴺ) →
    approx (+1d ∷ x) zero ℚP.- approx (-1d ∷ x) zero ≡ 1ℚ
  prefix-diff-zero x =
    cong₂ ℚP._-_ dCp≡h dCm≡-h ∙ ℚ!! ∙ two-h-is-one

  prefix-diff-suc : (x : 𝟛ᴺ) (m : ℕ) →
    approx (+1d ∷ x) (suc m) ℚP.- approx (-1d ∷ x) (suc m) ≡ 1ℚ
  prefix-diff-suc x m =
    cong₂ ℚP._-_ (approx-unfold (+1d ∷ x) m) (approx-unfold (-1d ∷ x) m)
    ∙ cancel-ab (digitContrib +1d zero) (digitContrib -1d zero)
               (inv2^ zero) (approx x m) (approx x m)
    ∙ cong (ℚP._+ inv2^ zero ℚP.· (approx x m ℚP.- approx x m))
           (cong₂ ℚP._-_ dCp≡h dCm≡-h)
    ∙ ℚ!! ∙ two-h-is-one

  prefix-diff : (x : 𝟛ᴺ) (n : ℕ) →
    approx (+1d ∷ x) n ℚP.- approx (-1d ∷ x) n ≡ 1ℚ
  prefix-diff x zero = prefix-diff-zero x
  prefix-diff x (suc m) = prefix-diff-suc x m

------------------------------------------------------------------------
-- Core bound: |approx(inc-aux d x)(n) - approx(+1d ∷ (d ∷ x))(n)| ≤ inv2^ n
------------------------------------------------------------------------

inc-aux-bound : (d : Digit) (x : 𝟛ᴺ) (n : ℕ) →
  abs (approx (inc-aux d x) n ℚP.- approx (+1d ∷ (d ∷ x)) n) ℚO.≤ inv2^ n

-- Base case (n = 0): the difference is between two digit contributions
inc-aux-bound -1d x zero =
  -- approx(inc-aux -1d x)(0) = digitContrib 0d 0
  -- approx(+1d ∷ (-1d ∷ x))(0) = digitContrib +1d 0
  -- diff = digitContrib 0d 0 - digitContrib +1d 0 = 0 - inv2^0 = -inv2^0
  -- |diff| = inv2^0 ≤ inv2^0
  subst (ℚO._≤ inv2^ zero)
    (sym (cong abs (cong₂ ℚP._-_ dC0≡0 dCp≡h ∙ zero-minus (inv2^ zero))
          ∙ abs-neg (inv2^ zero) ∙ abs-pos-inv2^ zero))
    (isRefl≤ (inv2^ zero))

inc-aux-bound 0d x zero =
  -- head(inc-aux 0d x) = +1d, so diff = digitContrib +1d 0 - digitContrib +1d 0 = 0
  subst (ℚO._≤ inv2^ zero)
    (sym (cong abs (self-minus (digitContrib +1d zero)) ∙ abs-0ℚ))
    (0≤inv2^ zero)

inc-aux-bound +1d x zero =
  -- head(inc-aux +1d x) = +1d, same as 0d case
  subst (ℚO._≤ inv2^ zero)
    (sym (cong abs (self-minus (digitContrib +1d zero)) ∙ abs-0ℚ))
    (0≤inv2^ zero)

-- Step case (suc n), d = 0d: both sides identical after approx-unfold
-- inc-aux 0d x has head +1d, tail = 0d ∷ x
-- +1d ∷ (0d ∷ x) has head +1d, tail = 0d ∷ x
-- So the approx-unfold of both gives the same expression.
inc-aux-bound 0d x (suc n) =
  let t = digitContrib +1d zero ℚP.+ inv2^ zero ℚP.· approx (0d ∷ x) n
      diff-eq : approx (inc-aux 0d x) (suc n) ℚP.- approx (+1d ∷ (0d ∷ x)) (suc n) ≡ 0ℚ
      diff-eq = cong₂ ℚP._-_ (approx-unfold (inc-aux 0d x) n)
                              (approx-unfold (+1d ∷ (0d ∷ x)) n)
              ∙ self-minus t
  in subst (ℚO._≤ inv2^ (suc n))
       (sym (cong abs diff-eq ∙ abs-0ℚ))
       (0≤inv2^ (suc n))

-- Step case (suc n), d = +1d: head digits match, scale IH by inv2^0
-- inc-aux +1d x has head +1d, tail = inc x
-- +1d ∷ (+1d ∷ x) has head +1d, tail = +1d ∷ x
-- diff = inv2^0 · (approx(inc x)(n) - approx(+1d ∷ x)(n))
inc-aux-bound +1d x (suc n) =
  let
    ih : abs (approx (inc-aux (head x) (tail x)) n
              ℚP.- approx (+1d ∷ (head x ∷ tail x)) n) ℚO.≤ inv2^ n
    ih = inc-aux-bound (head x) (tail x) n

    -- Transport IH along Stream-η: +1d ∷ (head x ∷ tail x) ≡ +1d ∷ x
    ih' : abs (approx (inc x) n ℚP.- approx (+1d ∷ x) n) ℚO.≤ inv2^ n
    ih' = subst (λ u → abs (approx (inc-aux (head x) (tail x)) n
                            ℚP.- approx (+1d ∷ u) n) ℚO.≤ inv2^ n)
                (sym (Stream-η {xs = x})) ih

    -- Decompose both sides via approx-unfold
    diff-eq : approx (inc-aux +1d x) (suc n) ℚP.- approx (+1d ∷ (+1d ∷ x)) (suc n)
            ≡ inv2^ zero ℚP.· (approx (inc x) n ℚP.- approx (+1d ∷ x) n)
    diff-eq = cong₂ ℚP._-_ (approx-unfold (inc-aux +1d x) n)
                            (approx-unfold (+1d ∷ (+1d ∷ x)) n)
            ∙ cancel-ab (digitContrib +1d zero) (digitContrib +1d zero)
                        (inv2^ zero) (approx (inc x) n) (approx (+1d ∷ x) n)
            ∙ cong (ℚP._+ inv2^ zero ℚP.· (approx (inc x) n ℚP.- approx (+1d ∷ x) n))
                   (self-minus (digitContrib +1d zero))
            ∙ ℚ!!

    -- Scale: |inv2^0 · t| = inv2^0 · |t|
    abs-eq : abs (approx (inc-aux +1d x) (suc n) ℚP.- approx (+1d ∷ (+1d ∷ x)) (suc n))
           ≡ inv2^ zero ℚP.· abs (approx (inc x) n ℚP.- approx (+1d ∷ x) n)
    abs-eq = cong abs diff-eq
           ∙ pos·abs (inv2^ zero) (approx (inc x) n ℚP.- approx (+1d ∷ x) n)
                     (0≤inv2^ zero)

    scaled : inv2^ zero ℚP.· abs (approx (inc x) n ℚP.- approx (+1d ∷ x) n)
             ℚO.≤ inv2^ (suc n)
    scaled = scale-bound (approx (inc x) n ℚP.- approx (+1d ∷ x) n) n ih'
  in subst (ℚO._≤ inv2^ (suc n)) (sym abs-eq) scaled

-- Step case (suc n), d = -1d: cancellation case
-- inc-aux -1d x has head 0d, tail = inc x
-- +1d ∷ (-1d ∷ x) has head +1d, tail = -1d ∷ x
-- diff = (dC₀ + h·A) - (dC₊ + h·C)
--      = (dC₀ - dC₊) + h·(A - C)     [cancel-ab]
--      = -h + h·(A - C)               [dC₀ = 0, dC₊ = h]
--      = -h + h·((A - B) + (B - C))   [add/subtract B]
--      = -h + h·(A-B) + h·(B-C)
-- Since B - C = 2h, h·(B-C) = 2h² = h, so -h + h·(A-B) + h = h·(A-B)
-- Algebraically: -h + h·((A-B) + 2h) = h·(A-B)  [by neg-cancel with "1" = 2h ... hmm]
-- Actually: the key ring identity is: -h + h·(t + 1) = h·t  [neg-cancel]
-- And B - C = 2·inv2^0 = 1 (by prefix-diff)
-- Wait, B - C = inv2^0 + inv2^0, not 1. Let me use the identity differently.
inc-aux-bound -1d x (suc n) =
  let
    ih : abs (approx (inc-aux (head x) (tail x)) n
              ℚP.- approx (+1d ∷ (head x ∷ tail x)) n) ℚO.≤ inv2^ n
    ih = inc-aux-bound (head x) (tail x) n

    ih' : abs (approx (inc x) n ℚP.- approx (+1d ∷ x) n) ℚO.≤ inv2^ n
    ih' = subst (λ u → abs (approx (inc-aux (head x) (tail x)) n
                            ℚP.- approx (+1d ∷ u) n) ℚO.≤ inv2^ n)
                (sym (Stream-η {xs = x})) ih

    h = inv2^ zero
    A = approx (inc x) n
    B = approx (+1d ∷ x) n
    C = approx (-1d ∷ x) n

    -- Step 1: decompose via approx-unfold
    diff-unfold : approx (inc-aux -1d x) (suc n) ℚP.- approx (+1d ∷ (-1d ∷ x)) (suc n)
                ≡ (digitContrib 0d zero ℚP.- digitContrib +1d zero) ℚP.+ h ℚP.· (A ℚP.- C)
    diff-unfold = cong₂ ℚP._-_ (approx-unfold (inc-aux -1d x) n)
                                (approx-unfold (+1d ∷ (-1d ∷ x)) n)
               ∙ cancel-ab (digitContrib 0d zero) (digitContrib +1d zero) h A C

    -- Step 2: digit contributions simplify to -h
    digit-eq : digitContrib 0d zero ℚP.- digitContrib +1d zero ≡ ℚP.- h
    digit-eq = cong₂ ℚP._-_ dC0≡0 dCp≡h ∙ zero-minus h

    -- Step 3: A - C = (A - B) + (B - C)
    split-diff : A ℚP.- C ≡ (A ℚP.- B) ℚP.+ (B ℚP.- C)
    split-diff = ℚ!!

    -- Step 4: B - C = 1ℚ (prefix-diff)
    bc-eq : B ℚP.- C ≡ 1ℚ
    bc-eq = prefix-diff x n

    -- Step 5: combine via neg-cancel: -h + h·((A-B) + 1) = h·(A-B)
    diff-eq : approx (inc-aux -1d x) (suc n) ℚP.- approx (+1d ∷ (-1d ∷ x)) (suc n)
            ≡ h ℚP.· (A ℚP.- B)
    diff-eq = diff-unfold
            ∙ cong₂ (λ a b → a ℚP.+ h ℚP.· b) digit-eq (split-diff ∙ cong ((A ℚP.- B) ℚP.+_) bc-eq)
            ∙ neg-cancel h (A ℚP.- B)

    abs-eq : abs (approx (inc-aux -1d x) (suc n) ℚP.- approx (+1d ∷ (-1d ∷ x)) (suc n))
           ≡ h ℚP.· abs (A ℚP.- B)
    abs-eq = cong abs diff-eq ∙ pos·abs h (A ℚP.- B) (0≤inv2^ zero)

    scaled : h ℚP.· abs (A ℚP.- B) ℚO.≤ inv2^ (suc n)
    scaled = scale-bound (A ℚP.- B) n ih'
  in subst (ℚO._≤ inv2^ (suc n)) (sym abs-eq) scaled

------------------------------------------------------------------------
-- Semantic equality: stream→ℝ (inc s) ≡ stream→ℝ (+1d ∷ s)
------------------------------------------------------------------------
-- Wraps inc-aux-bound with eqℝ + lim-lim, following the cons-resp pattern.

inc-sem : (s : 𝟛ᴺ) → stream→ℝ (inc s) ≡ stream→ℝ (+1d ∷ s)
inc-sem s = eqℝ _ _ close-all
  where
  -- Work with inc-aux (head s) (tail s) and +1d ∷ (head s ∷ tail s),
  -- then transport along Stream-η.
  d = head s
  x = tail s

  close-all : ∀ ε → stream→ℝ (inc s) ∼[ ε ] stream→ℝ (+1d ∷ s)
  close-all ε =
    lim-lim (λ δ → rat (approxℚ₊ (inc s) δ))
            (λ δ → rat (approxℚ₊ (+1d ∷ s) δ))
            ε δ₀ δ₀
            (approxℚ₊-cauchy (inc s))
            (approxℚ₊-cauchy (+1d ∷ s))
            v
            inner-close
    where
    δ₀ : ℚ₊
    δ₀ = /3₊ ε

    inner-eq : fst δ₀ ≡ fst ε ℚP.- (fst δ₀ ℚP.+ fst δ₀)
    inner-eq = ℚ!!

    v : 0< (fst ε ℚP.- (fst δ₀ ℚP.+ fst δ₀))
    v = subst (0<_) inner-eq (snd δ₀)

    n = ℚ₊→ℕ δ₀

    bound-raw : abs (approx (inc-aux d x) n ℚP.- approx (+1d ∷ (d ∷ x)) n)
                ℚO.≤ inv2^ n
    bound-raw = inc-aux-bound d x n

    bound : abs (approxℚ₊ (inc s) δ₀ ℚP.- approxℚ₊ (+1d ∷ s) δ₀)
            ℚO.≤ inv2^ n
    bound = subst (λ u → abs (approxℚ₊ (inc-aux d x) δ₀
                              ℚP.- approxℚ₊ (+1d ∷ u) δ₀) ℚO.≤ inv2^ n)
                  (sym (Stream-η {xs = s})) bound-raw

    strict : abs (approxℚ₊ (inc s) δ₀ ℚP.- approxℚ₊ (+1d ∷ s) δ₀)
             ℚO.< fst δ₀
    strict = isTrans≤< _ _ _ bound (modulus-correct δ₀)

    inner-close : rat (approxℚ₊ (inc s) δ₀)
                  ∼[ (fst ε ℚP.- (fst δ₀ ℚP.+ fst δ₀)) , v ]
                  rat (approxℚ₊ (+1d ∷ s) δ₀)
    inner-close = subst∼ inner-eq
      (rat-rat-fromAbs (approxℚ₊ (inc s) δ₀) (approxℚ₊ (+1d ∷ s) δ₀) δ₀
        strict)

------------------------------------------------------------------------
-- dec semantic correctness (symmetric to inc)
------------------------------------------------------------------------

dec-aux-bound : (d : Digit) (x : 𝟛ᴺ) (n : ℕ) →
  abs (approx (dec-aux d x) n ℚP.- approx (-1d ∷ (d ∷ x)) n) ℚO.≤ inv2^ n

-- Base case (n = 0)
dec-aux-bound +1d x zero =
  -- diff = digitContrib 0d 0 - digitContrib -1d 0 = 0 - (-inv2^0) = inv2^0
  let step : digitContrib 0d zero ℚP.- digitContrib -1d zero ≡ inv2^ zero
      step = cong₂ ℚP._-_ dC0≡0 dCm≡-h ∙ ℚ!!
  in subst (ℚO._≤ inv2^ zero)
       (sym (cong abs step ∙ abs-pos-inv2^ zero))
       (isRefl≤ (inv2^ zero))

dec-aux-bound 0d x zero =
  -- head(dec-aux 0d x) = -1d, diff = digitContrib -1d 0 - digitContrib -1d 0 = 0
  subst (ℚO._≤ inv2^ zero)
    (sym (cong abs (self-minus (digitContrib -1d zero)) ∙ abs-0ℚ))
    (0≤inv2^ zero)

dec-aux-bound -1d x zero =
  -- head(dec-aux -1d x) = -1d, same as 0d case
  subst (ℚO._≤ inv2^ zero)
    (sym (cong abs (self-minus (digitContrib -1d zero)) ∙ abs-0ℚ))
    (0≤inv2^ zero)

-- Step case d = 0d: both sides identical
dec-aux-bound 0d x (suc n) =
  let t = digitContrib -1d zero ℚP.+ inv2^ zero ℚP.· approx (0d ∷ x) n
      diff-eq : approx (dec-aux 0d x) (suc n) ℚP.- approx (-1d ∷ (0d ∷ x)) (suc n) ≡ 0ℚ
      diff-eq = cong₂ ℚP._-_ (approx-unfold (dec-aux 0d x) n)
                              (approx-unfold (-1d ∷ (0d ∷ x)) n)
              ∙ self-minus t
  in subst (ℚO._≤ inv2^ (suc n))
       (sym (cong abs diff-eq ∙ abs-0ℚ))
       (0≤inv2^ (suc n))

-- Step case d = -1d: head digits match (-1d), scale IH
dec-aux-bound -1d x (suc n) =
  let
    ih : abs (approx (dec-aux (head x) (tail x)) n
              ℚP.- approx (-1d ∷ (head x ∷ tail x)) n) ℚO.≤ inv2^ n
    ih = dec-aux-bound (head x) (tail x) n

    ih' : abs (approx (dec x) n ℚP.- approx (-1d ∷ x) n) ℚO.≤ inv2^ n
    ih' = subst (λ u → abs (approx (dec-aux (head x) (tail x)) n
                            ℚP.- approx (-1d ∷ u) n) ℚO.≤ inv2^ n)
                (sym (Stream-η {xs = x})) ih

    diff-eq : approx (dec-aux -1d x) (suc n) ℚP.- approx (-1d ∷ (-1d ∷ x)) (suc n)
            ≡ inv2^ zero ℚP.· (approx (dec x) n ℚP.- approx (-1d ∷ x) n)
    diff-eq = cong₂ ℚP._-_ (approx-unfold (dec-aux -1d x) n)
                            (approx-unfold (-1d ∷ (-1d ∷ x)) n)
            ∙ cancel-ab (digitContrib -1d zero) (digitContrib -1d zero)
                        (inv2^ zero) (approx (dec x) n) (approx (-1d ∷ x) n)
            ∙ cong (ℚP._+ inv2^ zero ℚP.· (approx (dec x) n ℚP.- approx (-1d ∷ x) n))
                   (self-minus (digitContrib -1d zero))
            ∙ ℚ!!

    abs-eq : abs (approx (dec-aux -1d x) (suc n) ℚP.- approx (-1d ∷ (-1d ∷ x)) (suc n))
           ≡ inv2^ zero ℚP.· abs (approx (dec x) n ℚP.- approx (-1d ∷ x) n)
    abs-eq = cong abs diff-eq
           ∙ pos·abs (inv2^ zero) (approx (dec x) n ℚP.- approx (-1d ∷ x) n)
                     (0≤inv2^ zero)

    scaled : inv2^ zero ℚP.· abs (approx (dec x) n ℚP.- approx (-1d ∷ x) n)
             ℚO.≤ inv2^ (suc n)
    scaled = scale-bound (approx (dec x) n ℚP.- approx (-1d ∷ x) n) n ih'
  in subst (ℚO._≤ inv2^ (suc n)) (sym abs-eq) scaled

-- Step case d = +1d: cancellation (symmetric to inc's -1d case)
-- dec-aux +1d x has head 0d, tail = dec x
-- -1d ∷ (+1d ∷ x) has head -1d, tail = +1d ∷ x
-- diff = (dC₀ - dC₋) + h·(A - C) = h + h·((A-B) + (-1)) = h·(A-B) via pos-cancel
dec-aux-bound +1d x (suc n) =
  let
    ih : abs (approx (dec-aux (head x) (tail x)) n
              ℚP.- approx (-1d ∷ (head x ∷ tail x)) n) ℚO.≤ inv2^ n
    ih = dec-aux-bound (head x) (tail x) n

    ih' : abs (approx (dec x) n ℚP.- approx (-1d ∷ x) n) ℚO.≤ inv2^ n
    ih' = subst (λ u → abs (approx (dec-aux (head x) (tail x)) n
                            ℚP.- approx (-1d ∷ u) n) ℚO.≤ inv2^ n)
                (sym (Stream-η {xs = x})) ih

    h = inv2^ zero
    A = approx (dec x) n
    B = approx (-1d ∷ x) n
    C = approx (+1d ∷ x) n

    diff-unfold : approx (dec-aux +1d x) (suc n) ℚP.- approx (-1d ∷ (+1d ∷ x)) (suc n)
                ≡ (digitContrib 0d zero ℚP.- digitContrib -1d zero) ℚP.+ h ℚP.· (A ℚP.- C)
    diff-unfold = cong₂ ℚP._-_ (approx-unfold (dec-aux +1d x) n)
                                (approx-unfold (-1d ∷ (+1d ∷ x)) n)
               ∙ cancel-ab (digitContrib 0d zero) (digitContrib -1d zero) h A C

    digit-eq : digitContrib 0d zero ℚP.- digitContrib -1d zero ≡ h
    digit-eq = cong₂ ℚP._-_ dC0≡0 dCm≡-h ∙ ℚ!!

    split-diff : A ℚP.- C ≡ (A ℚP.- B) ℚP.+ (B ℚP.- C)
    split-diff = ℚ!!

    -- B - C = -(C - B) = -(prefix-diff x n) = -1ℚ
    bc-eq : B ℚP.- C ≡ ℚP.- 1ℚ
    bc-eq = minus-flip B C ∙ cong ℚP.-_ (prefix-diff x n)

    diff-eq : approx (dec-aux +1d x) (suc n) ℚP.- approx (-1d ∷ (+1d ∷ x)) (suc n)
            ≡ h ℚP.· (A ℚP.- B)
    diff-eq = diff-unfold
            ∙ cong₂ (λ a b → a ℚP.+ h ℚP.· b) digit-eq
                     (split-diff ∙ cong ((A ℚP.- B) ℚP.+_) bc-eq)
            ∙ pos-cancel h (A ℚP.- B)

    abs-eq : abs (approx (dec-aux +1d x) (suc n) ℚP.- approx (-1d ∷ (+1d ∷ x)) (suc n))
           ≡ h ℚP.· abs (A ℚP.- B)
    abs-eq = cong abs diff-eq ∙ pos·abs h (A ℚP.- B) (0≤inv2^ zero)

    scaled : h ℚP.· abs (A ℚP.- B) ℚO.≤ inv2^ (suc n)
    scaled = scale-bound (A ℚP.- B) n ih'
  in subst (ℚO._≤ inv2^ (suc n)) (sym abs-eq) scaled

------------------------------------------------------------------------
-- dec semantic equality
------------------------------------------------------------------------

dec-sem : (s : 𝟛ᴺ) → stream→ℝ (dec s) ≡ stream→ℝ (-1d ∷ s)
dec-sem s = eqℝ _ _ close-all
  where
  d = head s
  x = tail s

  close-all : ∀ ε → stream→ℝ (dec s) ∼[ ε ] stream→ℝ (-1d ∷ s)
  close-all ε =
    lim-lim (λ δ → rat (approxℚ₊ (dec s) δ))
            (λ δ → rat (approxℚ₊ (-1d ∷ s) δ))
            ε δ₀ δ₀
            (approxℚ₊-cauchy (dec s))
            (approxℚ₊-cauchy (-1d ∷ s))
            v
            inner-close
    where
    δ₀ : ℚ₊
    δ₀ = /3₊ ε

    inner-eq : fst δ₀ ≡ fst ε ℚP.- (fst δ₀ ℚP.+ fst δ₀)
    inner-eq = ℚ!!

    v : 0< (fst ε ℚP.- (fst δ₀ ℚP.+ fst δ₀))
    v = subst (0<_) inner-eq (snd δ₀)

    n = ℚ₊→ℕ δ₀

    bound-raw : abs (approx (dec-aux d x) n ℚP.- approx (-1d ∷ (d ∷ x)) n)
                ℚO.≤ inv2^ n
    bound-raw = dec-aux-bound d x n

    bound : abs (approxℚ₊ (dec s) δ₀ ℚP.- approxℚ₊ (-1d ∷ s) δ₀)
            ℚO.≤ inv2^ n
    bound = subst (λ u → abs (approxℚ₊ (dec-aux d x) δ₀
                              ℚP.- approxℚ₊ (-1d ∷ u) δ₀) ℚO.≤ inv2^ n)
                  (sym (Stream-η {xs = s})) bound-raw

    strict : abs (approxℚ₊ (dec s) δ₀ ℚP.- approxℚ₊ (-1d ∷ s) δ₀)
             ℚO.< fst δ₀
    strict = isTrans≤< _ _ _ bound (modulus-correct δ₀)

    inner-close : rat (approxℚ₊ (dec s) δ₀)
                  ∼[ (fst ε ℚP.- (fst δ₀ ℚP.+ fst δ₀)) , v ]
                  rat (approxℚ₊ (-1d ∷ s) δ₀)
    inner-close = subst∼ inner-eq
      (rat-rat-fromAbs (approxℚ₊ (dec s) δ₀) (approxℚ₊ (-1d ∷ s) δ₀) δ₀
        strict)

------------------------------------------------------------------------
-- The 4 proved properties (replacing postulates)
------------------------------------------------------------------------

inc-resp : (s t : 𝟛ᴺ) → s ≈sd t → inc s ≈sd inc t
inc-resp s t h = inc-sem s ∙ cons-resp +1d s t h ∙ sym (inc-sem t)

dec-resp : (s t : 𝟛ᴺ) → s ≈sd t → dec s ≈sd dec t
dec-resp s t h = dec-sem s ∙ cons-resp -1d s t h ∙ sym (dec-sem t)

carry-raw : (s : 𝟛ᴺ) → (+1d ∷ (-1d ∷ s)) ≈sd (0d ∷ inc s)
carry-raw s = sym (inc-sem (-1d ∷ s))
            ∙ cong stream→ℝ (Stream-η {xs = inc-aux -1d s})

borrow-raw : (s : 𝟛ᴺ) → (-1d ∷ (+1d ∷ s)) ≈sd (0d ∷ dec s)
borrow-raw s = sym (dec-sem (+1d ∷ s))
             ∙ cong stream→ℝ (Stream-η {xs = dec-aux +1d s})

------------------------------------------------------------------------
-- Quotient lifts
------------------------------------------------------------------------

inc𝕀 : 𝕀sd → 𝕀sd
inc𝕀 = SQ.rec isSet𝕀sd (λ s → [ inc s ]sd)
  (λ s t h → eq/ (inc s) (inc t) (inc-resp s t h))

dec𝕀 : 𝕀sd → 𝕀sd
dec𝕀 = SQ.rec isSet𝕀sd (λ s → [ dec s ]sd)
  (λ s t h → eq/ (dec s) (dec t) (dec-resp s t h))

------------------------------------------------------------------------
-- Carry/borrow equations in 𝕀sd
------------------------------------------------------------------------

carry𝕀 : (s : 𝟛ᴺ) → [ +1d ∷ (-1d ∷ s) ]sd ≡ [ 0d ∷ inc s ]sd
carry𝕀 s = eq/ (+1d ∷ (-1d ∷ s)) (0d ∷ inc s) (carry-raw s)

borrow𝕀 : (s : 𝟛ᴺ) → [ -1d ∷ (+1d ∷ s) ]sd ≡ [ 0d ∷ dec s ]sd
borrow𝕀 s = eq/ (-1d ∷ (+1d ∷ s)) (0d ∷ dec s) (borrow-raw s)
