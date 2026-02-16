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

open import Cubical.Codata.Stream as StreamM using (Stream; _,_)
open StreamM.Stream

open import Cubical.HITs.SetQuotients as SQ

open import Cubical.HITs.CauchyReals.Base using (ℝ; rat; lim; eqℝ)
open import Cubical.HITs.CauchyReals.Closeness using (isSetℝ)

open import Reals.SignedDigit.Core
open import Reals.SignedDigit.Bounded
  using ( stream→ℝ; _≈sd_; 𝕀sd; [_]sd; isSet𝕀sd
        ; stream→ℝ-resp; ι )

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
-- Semantic correctness (postulated)
------------------------------------------------------------------------
-- These state that inc/dec act as affine maps on the semantic value.
-- Proof requires relating Cauchy-real limits of digit-contribution
-- partial sums — deferred to avoid blocking downstream development.

-- TODO: the full semantic correctness statements
--   inc-sem : (s : 𝟛ᴺ) → stream→ℝ (inc s) ≡ (1/2 +ℝ stream→ℝ s /ℝ 2)
--   dec-sem : (s : 𝟛ᴺ) → stream→ℝ (dec s) ≡ (-1/2 +ℝ stream→ℝ s /ℝ 2)
-- require ℝ arithmetic (addition, scalar multiplication) which is not
-- yet available in this codebase. We postulate the weaker "preserves ≈sd"
-- properties below, from which the quotient lifts follow.

------------------------------------------------------------------------
-- inc/dec respect the equivalence relation
------------------------------------------------------------------------
-- Key property: if s ≈sd t (i.e., stream→ℝ s ≡ stream→ℝ t), then
-- inc s ≈sd inc t (i.e., stream→ℝ (inc s) ≡ stream→ℝ (inc t)).
--
-- Proof strategy: both stream→ℝ (inc s) and stream→ℝ (inc t)
-- equal the same affine transform of the shared semantic value.
-- Since s ≈sd t means stream→ℝ s ≡ stream→ℝ t, and
-- stream→ℝ (inc s) depends only on stream→ℝ s (up to the affine map),
-- the result follows by congruence.

-- POSTULATE: requires the full inc-sem proof
postulate
  inc-resp : (s t : 𝟛ᴺ) → s ≈sd t → inc s ≈sd inc t
  dec-resp : (s t : 𝟛ᴺ) → s ≈sd t → dec s ≈sd dec t

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
-- Carry/borrow equations on raw streams (up to ≈sd)
------------------------------------------------------------------------
-- These are the semantic content of Altenkirch's carry/borrow:
--   carry:  +1 ∷ (-1 ∷ s) ≈sd 0 ∷ inc s
--   borrow: -1 ∷ (+1 ∷ s) ≈sd 0 ∷ dec s
--
-- Proof: both sides have the same semantic value.
--   LHS carry:  1/2 + (-1/2 + ⟦s⟧/2)/2 = 1/4 + ⟦s⟧/4
--   RHS carry:  0 + (1/2 + ⟦s⟧/2)/2    = 1/4 + ⟦s⟧/4

-- POSTULATE: requires rational/real arithmetic on Cauchy limits
postulate
  carry-raw : (s : 𝟛ᴺ) → (+1d ∷ (-1d ∷ s)) ≈sd (0d ∷ inc s)
  borrow-raw : (s : 𝟛ᴺ) → (-1d ∷ (+1d ∷ s)) ≈sd (0d ∷ dec s)

------------------------------------------------------------------------
-- Carry/borrow equations in 𝕀sd
------------------------------------------------------------------------

carry𝕀 : (s : 𝟛ᴺ) → [ +1d ∷ (-1d ∷ s) ]sd ≡ [ 0d ∷ inc s ]sd
carry𝕀 s = eq/ (+1d ∷ (-1d ∷ s)) (0d ∷ inc s) (carry-raw s)

borrow𝕀 : (s : 𝟛ᴺ) → [ -1d ∷ (+1d ∷ s) ]sd ≡ [ 0d ∷ dec s ]sd
borrow𝕀 s = eq/ (-1d ∷ (+1d ∷ s)) (0d ∷ dec s) (borrow-raw s)
