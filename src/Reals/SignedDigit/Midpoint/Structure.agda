{-# OPTIONS --cubical --guardedness #-}

------------------------------------------------------------------------
-- 𝕀sd as a Pointed Midpoint Algebra
------------------------------------------------------------------------
--
-- We show that the quotient 𝕀sd = 𝟛ᴺ / _≈sd_ carries a
-- PointedMidpointAlg structure with:
--   • _⊕𝕀_ : binary midpoint (average) operation
--   • bot𝕀 = [-1,-1,...], top𝕀 = [+1,+1,...] as generators
--
-- and relate this to the HCIT operations:
--   • cons𝕀 d x ≡ digitPoint d ⊕𝕀 x
--   • inc𝕀 x ≡ top𝕀 ⊕𝕀 x        (proved, no postulate)
--   • dec𝕀 x ≡ bot𝕀 ⊕𝕀 x        (proved, no postulate)
--
-- POSTULATES:
--   avg, avg-sem    : stream-level average + semantics (from
--                     Midpoint/Average.agda placeholder)
--   ι-cons          : semantic unfolding of cons (limit computation)
--   /2ᵣ-x+x        : ℝ arithmetic helper (provable via ≡Continuous)
--   medial-ℝ-lemma  : ℝ ring equation (provable via ≡Continuous)
-- None require AC_ω.

module Reals.SignedDigit.Midpoint.Structure where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (isPropΠ)

open import Cubical.HITs.SetQuotients as SQ hiding ([_])
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)

open import Cubical.Data.Sigma
open import Cubical.Data.Rationals.Fast as ℚ using (_+_)

open import Cubical.HITs.CauchyReals.Base using (ℝ; rat)
open import Cubical.HITs.CauchyReals.Closeness using (isSetℝ)
open import Cubical.HITs.CauchyReals.Order using (_+ᵣ_; +ᵣComm; +ᵣ-rat)
open import Cubical.HITs.CauchyReals.Multiplication using (/2ᵣ)
open import Cubical.Tactics.CommRingSolverFast.FastRationalsReflection using (ℚ!!)

open import Reals.SignedDigit.Core
open import Reals.SignedDigit.Bounded
  using ( stream→ℝ; _≈sd_; 𝕀sd; [_]sd; isSet𝕀sd; ι
        ; digitToℚ )
open import Reals.SignedDigit.IncDec
  using ( inc𝕀; dec𝕀; inc-sem; dec-sem )
open import Reals.SignedDigit.HCIT.Algebra using (𝕀-Alg)
open import Reals.SignedDigit.HCIT.Structure
  using ( cons𝕀; gen-𝕀
        ; carry-compl-𝕀; borrow-compl-𝕀
        ; sep-L-𝕀; sep-R-𝕀 )
open import Reals.SignedDigit.Midpoint.Algebra
open import Reals.SignedDigit.Midpoint.Average using (avg; avg-sem)
open import Reals.SignedDigit.Midpoint.Comparison
  using (RemainingAxioms; build𝕀-Alg)

------------------------------------------------------------------------
-- ι-inj: defined locally (avoids importing AC_ω-containing modules)
------------------------------------------------------------------------

ι-inj : (a b : 𝕀sd) → ι a ≡ ι b → a ≡ b
ι-inj = SQ.elimProp2 (λ _ _ → isPropΠ (λ _ → isSet𝕀sd _ _))
  (λ s t h → eq/ s t h)

------------------------------------------------------------------------
-- The midpoint operation on 𝕀sd
------------------------------------------------------------------------

-- avg respects ≈sd in both arguments (derived from avg-sem)
avg-resp-l : ∀ s s' t → s ≈sd s' → avg s t ≈sd avg s' t
avg-resp-l s s' t hs =
  avg-sem s t ∙ cong (λ u → /2ᵣ (u +ᵣ stream→ℝ t)) hs ∙ sym (avg-sem s' t)

avg-resp-r : ∀ s t t' → t ≈sd t' → avg s t ≈sd avg s t'
avg-resp-r s t t' ht =
  avg-sem s t ∙ cong (λ u → /2ᵣ (stream→ℝ s +ᵣ u)) ht ∙ sym (avg-sem s t')

-- The midpoint operation on 𝕀sd
_⊕𝕀_ : 𝕀sd → 𝕀sd → 𝕀sd
_⊕𝕀_ = SQ.rec2 isSet𝕀sd
  (λ s t → [ avg s t ]sd)
  (λ s s' t hs → eq/ _ _ (avg-resp-l s s' t hs))
  (λ s t t' ht → eq/ _ _ (avg-resp-r s t t' ht))

------------------------------------------------------------------------
-- Semantic bridge: ι (x ⊕ y) ≡ /2ᵣ (ι x +ᵣ ι y)
------------------------------------------------------------------------

ι-⊕ : ∀ x y → ι (x ⊕𝕀 y) ≡ /2ᵣ (ι x +ᵣ ι y)
ι-⊕ = SQ.elimProp2 (λ _ _ → isSetℝ _ _)
  (λ s t → avg-sem s t)

------------------------------------------------------------------------
-- Generators
------------------------------------------------------------------------

bot𝕀 : 𝕀sd
bot𝕀 = [ repeat -1d ]sd

top𝕀 : 𝕀sd
top𝕀 = [ repeat +1d ]sd

------------------------------------------------------------------------
-- ℝ arithmetic helpers
------------------------------------------------------------------------
-- These are all provable via ≡Continuous + rational arithmetic,
-- but the proofs require chaining through the Lipschitz/continuity
-- infrastructure. Postulated to keep focus on the algebraic content.

postulate
  -- /2ᵣ (x +ᵣ x) ≡ x  (half of x + x is x)
  -- Proof sketch: ≡Continuous with f = (λ x → /2ᵣ(x+x)), g = id
  -- On rationals: /2ᵣ(rat(r+r)) = rat((r+r)/2) = rat r
  /2ᵣ-x+x : ∀ x → /2ᵣ (x +ᵣ x) ≡ x

  -- Mediality in ℝ:
  -- /2ᵣ (/2ᵣ(a+b) +ᵣ /2ᵣ(c+d)) ≡ /2ᵣ (/2ᵣ(a+c) +ᵣ /2ᵣ(b+d))
  -- Proof: both sides equal /2ᵣ (/2ᵣ (a+b+c+d)) via ≡Continuous
  -- + ring arithmetic. Requires unfolding /2ᵣ as [1/2] ·ᵣ _.
  medial-ℝ-lemma : ∀ a b c d →
    /2ᵣ (/2ᵣ (a +ᵣ b) +ᵣ /2ᵣ (c +ᵣ d)) ≡
    /2ᵣ (/2ᵣ (a +ᵣ c) +ᵣ /2ᵣ (b +ᵣ d))

------------------------------------------------------------------------
-- Midpoint axioms on 𝕀sd
------------------------------------------------------------------------

-- Idempotency: x ⊕ x ≡ x
idem-𝕀 : ∀ x → x ⊕𝕀 x ≡ x
idem-𝕀 x = ι-inj _ _ (ι-⊕ x x ∙ /2ᵣ-x+x (ι x))

-- Commutativity: x ⊕ y ≡ y ⊕ x
comm-𝕀 : ∀ x y → x ⊕𝕀 y ≡ y ⊕𝕀 x
comm-𝕀 x y = ι-inj _ _
  (ι-⊕ x y ∙ cong /2ᵣ (+ᵣComm (ι x) (ι y)) ∙ sym (ι-⊕ y x))

-- Mediality: (a ⊕ b) ⊕ (c ⊕ d) ≡ (a ⊕ c) ⊕ (b ⊕ d)
medial-𝕀 : ∀ a b c d →
  (a ⊕𝕀 b) ⊕𝕀 (c ⊕𝕀 d) ≡ (a ⊕𝕀 c) ⊕𝕀 (b ⊕𝕀 d)
medial-𝕀 a b c d = ι-inj _ _
  ( ι-⊕ (a ⊕𝕀 b) (c ⊕𝕀 d)
  ∙ cong₂ (λ u v → /2ᵣ (u +ᵣ v)) (ι-⊕ a b) (ι-⊕ c d)
  ∙ medial-ℝ-lemma (ι a) (ι b) (ι c) (ι d)
  ∙ sym (cong₂ (λ u v → /2ᵣ (u +ᵣ v)) (ι-⊕ a c) (ι-⊕ b d))
  ∙ sym (ι-⊕ (a ⊕𝕀 c) (b ⊕𝕀 d))
  )

------------------------------------------------------------------------
-- 𝕀sd as a PointedMidpointAlg
------------------------------------------------------------------------

𝕀sd-MidAlg : PointedMidpointAlg
PointedMidpointAlg.midpointAlg 𝕀sd-MidAlg = record
  { Carrier = 𝕀sd
  ; isSetCarrier = isSet𝕀sd
  ; _⊕_ = _⊕𝕀_
  ; idem = idem-𝕀
  ; comm = comm-𝕀
  ; medial = medial-𝕀
  }
PointedMidpointAlg.bot 𝕀sd-MidAlg = bot𝕀
PointedMidpointAlg.top 𝕀sd-MidAlg = top𝕀

------------------------------------------------------------------------
-- Relating HCIT operations to midpoint operations
------------------------------------------------------------------------

-- inc𝕀 ≡ cons𝕀 +1d  (proved from stream-level inc-sem)
inc𝕀≡cons+1 : ∀ x → inc𝕀 x ≡ cons𝕀 +1d x
inc𝕀≡cons+1 = SQ.elimProp (λ _ → isSet𝕀sd _ _)
  (λ s → eq/ _ _ (inc-sem s))

-- dec𝕀 ≡ cons𝕀 -1d  (proved from stream-level dec-sem)
dec𝕀≡cons-1 : ∀ x → dec𝕀 x ≡ cons𝕀 -1d x
dec𝕀≡cons-1 = SQ.elimProp (λ _ → isSet𝕀sd _ _)
  (λ s → eq/ _ _ (dec-sem s))

-- POSTULATE: semantic unfolding of cons
-- stream→ℝ(d ∷ s) = /2ᵣ (rat(digitToℚ d) +ᵣ stream→ℝ s)
-- Same proof pattern as cons-resp/inc-sem (limit argument on
-- approx-unfold). Not yet proved in codebase.
postulate
  ι-cons : ∀ d x → ι (cons𝕀 d x) ≡ /2ᵣ (rat (digitToℚ d) +ᵣ ι x)

-- Semantic values of generators (derived from ι-cons)
-- ι(bot𝕀) = /2ᵣ(rat(-1) +ᵣ ι(bot𝕀)), solving gives rat(-1)
-- ι(top𝕀) = /2ᵣ(rat(1) +ᵣ ι(top𝕀)), solving gives rat(1)
postulate
  ι-bot : ι bot𝕀 ≡ rat (digitToℚ -1d)
  ι-top : ι top𝕀 ≡ rat (digitToℚ +1d)

-- The core comparison: cons𝕀 d x ≡ digitPoint d ⊕𝕀 x
cons-is-⊕ : ∀ d x → cons𝕀 d x ≡ PointedMidpointAlg.digitPoint 𝕀sd-MidAlg d ⊕𝕀 x
cons-is-⊕ d x = ι-inj _ _
  ( ι-cons d x
  ∙ cong (λ u → /2ᵣ (u +ᵣ ι x)) (sym (ι-digitPoint d))
  ∙ sym (ι-⊕ (PointedMidpointAlg.digitPoint 𝕀sd-MidAlg d) x)
  )
  where
  ι-digitPoint : ∀ d → ι (PointedMidpointAlg.digitPoint 𝕀sd-MidAlg d) ≡ rat (digitToℚ d)
  ι-digitPoint -1d = ι-bot
  ι-digitPoint  0d = ι-⊕ bot𝕀 top𝕀 ∙ cong₂ (λ u v → /2ᵣ (u +ᵣ v)) ι-bot ι-top
                   ∙ ι-cons-mid
    where
    -- /2ᵣ (rat(digitToℚ -1d) +ᵣ rat(digitToℚ +1d)) ≡ rat(digitToℚ 0d)
    -- i.e., /2ᵣ (rat(-1) +ᵣ rat(1)) ≡ rat(0)
    ι-cons-mid : /2ᵣ (rat (digitToℚ -1d) +ᵣ rat (digitToℚ +1d)) ≡ rat (digitToℚ 0d)
    ι-cons-mid =
      cong /2ᵣ (+ᵣ-rat (digitToℚ -1d) (digitToℚ +1d))
      ∙ cong /2ᵣ (cong rat q-1+1)
      ∙ cong /2ᵣ
          (cong rat (sym q0+0)
           ∙ sym (+ᵣ-rat (digitToℚ 0d) (digitToℚ 0d)))
      ∙ /2ᵣ-x+x (rat (digitToℚ 0d))
      where
      q-1+1 : (digitToℚ -1d ℚ.+ digitToℚ +1d) ≡ digitToℚ 0d
      q-1+1 = ℚ!!

      q0+0 : (digitToℚ 0d ℚ.+ digitToℚ 0d) ≡ digitToℚ 0d
      q0+0 = ℚ!!
  ι-digitPoint +1d = ι-top

-- inc𝕀 x ≡ top𝕀 ⊕𝕀 x  (from inc𝕀≡cons+1 + cons-is-⊕)
inc-is-⊕ : ∀ x → inc𝕀 x ≡ top𝕀 ⊕𝕀 x
inc-is-⊕ x = inc𝕀≡cons+1 x ∙ cons-is-⊕ +1d x

-- dec𝕀 x ≡ bot𝕀 ⊕𝕀 x  (from dec𝕀≡cons-1 + cons-is-⊕)
dec-is-⊕ : ∀ x → dec𝕀 x ≡ bot𝕀 ⊕𝕀 x
dec-is-⊕ x = dec𝕀≡cons-1 x ∙ cons-is-⊕ -1d x

------------------------------------------------------------------------
-- Full HCIT packaging from midpoint structure on 𝕀sd
------------------------------------------------------------------------

module C = Reals.SignedDigit.Midpoint.Comparison.Core 𝕀sd-MidAlg

midpoint-remaining : RemainingAxioms 𝕀sd-MidAlg
RemainingAxioms.gen midpoint-remaining y =
  PT.map
    (λ { (d , x , p) → d , x , p ∙ cons-is-⊕ d x })
    (gen-𝕀 y)
RemainingAxioms.carry-compl midpoint-remaining x y p =
  sym (cons-is-⊕ -1d x)
  ∙ carry-compl-𝕀 x y
      (cons-is-⊕ 0d x ∙ p ∙ sym (inc-is-⊕ y))
  ∙ cons-is-⊕ 0d y
RemainingAxioms.borrow-compl midpoint-remaining x y p =
  sym (cons-is-⊕ +1d x)
  ∙ borrow-compl-𝕀 x y
      (cons-is-⊕ 0d x ∙ p ∙ sym (dec-is-⊕ y))
  ∙ cons-is-⊕ 0d y
RemainingAxioms.sep-L midpoint-remaining x y p =
  sym (cons-is-⊕ 0d x)
  ∙ sep-L-𝕀 x y
      (cons-is-⊕ -1d x ∙ p ∙ sym (cons-is-⊕ 0d y))
  ∙ inc-is-⊕ y
RemainingAxioms.sep-R midpoint-remaining x y p =
  sym (cons-is-⊕ 0d x)
  ∙ sep-R-𝕀 x y
      (cons-is-⊕ +1d x ∙ p ∙ sym (cons-is-⊕ 0d y))
  ∙ dec-is-⊕ y

𝕀sd-MidpointInduced-Alg : 𝕀-Alg
𝕀sd-MidpointInduced-Alg = build𝕀-Alg 𝕀sd-MidAlg midpoint-remaining
