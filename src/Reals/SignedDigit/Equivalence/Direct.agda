{-# OPTIONS --cubical --guardedness --allow-unsolved-metas #-}

------------------------------------------------------------------------
-- Signed-Digit Equivalence: Direct Approach via Recℝ
------------------------------------------------------------------------
--
-- This module implements the direct embedding ℝ → 𝕀sd using the Recℝ
-- eliminator from Cauchy reals. This approach requires coherence
-- conditions (rat-lim-B, lim-rat-B, lim-lim-B) which are challenging
-- to prove.
--
-- KEY EXPORTS:
--   ι⁻¹            : ℝ → 𝕀sd (the inverse of the embedding)
--   ℝ→𝕀sd-direct   : Direct definition via Recℝ
--   fromℝ          : ℝ → ℝsd (full encoding with exponent)
--   ℝsd≃ℝ          : Type equivalence (postulated, depends on fromℝ-toℝ)
--
-- NOTE: This approach has unfilled coherence holes. Consider using
-- the Surjection approach (Equivalence.Surjection) instead.
--
------------------------------------------------------------------------

module Reals.SignedDigit.Equivalence.Direct where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (isPropΠ)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence

open import Cubical.Data.Int as ℤ using (ℤ; pos)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.HITs.SetQuotients as SQ hiding ([_])
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Data.Rationals.Fast as ℚ
open import Cubical.Data.Rationals.Fast.Properties as ℚP
open import Cubical.Data.Rationals.Fast.Order as ℚO
  using (ℚ₊; minus-<; isTrans<≤; isTrans<; ℚ₊≡; 0<ℚ₊)
open import Cubical.Data.Rationals.Fast.Order.Properties as ℚOP
  using (/2₊; ε/2+ε/2≡ε)

open import Cubical.HITs.CauchyReals.Base as ℝBase using (ℝ; rat; eqℝ; _∼[_]_; rat-rat-fromAbs; Recℝ)
open import Cubical.HITs.CauchyReals.Closeness using (triangle∼; sym∼)
open import Cubical.HITs.CauchyReals.Multiplication as ℝMul using (_·ᵣ_)

open import Reals.SignedDigit.Core
open import Reals.SignedDigit.Bounded using (𝕀sd; _≈sd_; isSet𝕀sd; stream→ℝ; rational→stream; clampℚ; clamp-lip; ι; -1ℚ; +1ℚ; 0ℚ)
open import Reals.SignedDigit.Representation using (ℝsd-raw; ℝsd; toℝ; toℝ-raw; pow2ℤ; isSetℝsd)
open import Reals.SignedDigit.Equivalence.Helpers using (ℝ∈OpenUnit; val; choose-k; 1ℚ₊)
open import Reals.SignedDigit.Equivalence.RoundTrip using (round-trip-clamped)
open import Reals.SignedDigit.Limit using (limA-𝕀sd; limA-𝕀sd-close)

-- Alias for ℚ₊ addition
_+₊_ : ℚ₊ → ℚ₊ → ℚ₊
_+₊_ = ℚO._ℚ₊+_

------------------------------------------------------------------------
-- The B relation for Recℝ
------------------------------------------------------------------------

-- We use 2ε-closeness in ℝ via the embedding ι.
-- The factor of 2 is necessary to absorb the error from the coinductive
-- limit construction: limA-𝕀sd-close gives a bound of δ + δ = 2δ.
--
-- With B a a' ε = ι a ∼[2ε] ι a', the coherence proofs work:
-- - rat-lim-B: (ε - δ) + 2δ = ε + δ ≤ 2ε when δ ≤ ε/2 (achievable)
-- - Actually: 2(ε - δ) + 2δ = 2ε exactly! (with modified coherence input)
--
-- The factor of 2 doesn't affect the final equivalence since closeness
-- for all ε implies closeness for all 2ε (and vice versa).
𝕀sd-B : 𝕀sd → 𝕀sd → ℚ₊ → Type₀
𝕀sd-B a a' ε = ι a ∼[ ε +₊ ε ] ι a'

------------------------------------------------------------------------
-- ι-inj: quotient injectivity
------------------------------------------------------------------------

-- If ι a ≡ ι a', then a ≡ a' in 𝕀sd
-- This follows from the definition of ι and ≈sd:
--   ι = SQ.rec isSetℝ stream→ℝ stream→ℝ-resp
--   _≈sd_ = stream→ℝ x ≡ stream→ℝ y
-- So ι [s] = stream→ℝ s, and ι [s] ≡ ι [t] gives stream→ℝ s ≡ stream→ℝ t = s ≈sd t
-- By eq/, this gives [s] ≡ [t]
ι-inj : ∀ a a' → ι a ≡ ι a' → a ≡ a'
ι-inj = SQ.elimProp2
          (λ a a' → isPropΠ (λ _ → isSet𝕀sd a a'))
          (λ s t h → eq/ s t h)

------------------------------------------------------------------------
-- isProp∼: closeness is a proposition
------------------------------------------------------------------------

-- FIXME: The closeness relation _∼[_]_ is defined recursively on the HIT structure.
-- Proving isProp requires understanding how ∼ is defined in the library.
-- For now, leave as a hole - it should follow from the library's definitions.
isProp∼ : (x y : ℝ) (ε : ℚO.ℚ₊) → isProp (x ∼[ ε ] y)
isProp∼ x y ε = {!   !}

------------------------------------------------------------------------
-- Building the Recℝ structure for ℝ → 𝕀sd
------------------------------------------------------------------------

-- Helper: ε/2 + ε/2 ≡ ε (as ℚ₊)
/2₊+/2₊≡ε₊ : ∀ ε → /2₊ ε +₊ /2₊ ε ≡ ε
/2₊+/2₊≡ε₊ ε = ℚO.ℚ₊≡ (ε/2+ε/2≡ε (fst ε))

-- Helper: (δ + ε)/2 = δ/2 + ε/2 (distributivity of /2₊ over +₊)
-- Proof: (δ + ε) · 1/2 = δ · 1/2 + ε · 1/2 by ·DistR+
-- Note: We use fst (1ℚ₊) = 1 as the unit since we don't have direct 1/2 syntax here
-- Actually, /2₊ ε = ε · [1/2], so fst (/2₊ ε) = fst ε · [1/2]
-- We can avoid explicit 1/2 by using the definition directly.
/2₊-dist : ∀ δ ε → /2₊ (δ +₊ ε) ≡ /2₊ δ +₊ /2₊ ε
/2₊-dist δ ε = ℚO.ℚ₊≡ eq
  where
    -- /2₊ is defined as _ℚ₊· ([ 1 / 2 ] , tt)
    -- So /2₊ (δ +₊ ε) = (δ + ε) · [1/2]
    -- And /2₊ δ +₊ /2₊ ε = (δ · [1/2]) + (ε · [1/2])
    -- By ·DistR+: (δ + ε) · [1/2] = δ · [1/2] + ε · [1/2]
    -- The proof is just this equality at the rational level
    open import Cubical.Data.Rationals.Fast.Base as ℚB using ([_/_])
    open import Cubical.Data.NatPlusOne using (1+_)
    half : ℚ.ℚ
    half = ℚB.[_/_] (pos 1) (1+ 1)  -- 1/2 where denominator is ℕ₊₁
    eq : fst (/2₊ (δ +₊ ε)) ≡ fst (/2₊ δ +₊ /2₊ ε)
    eq = ℚP.·DistR+ (fst δ) (fst ε) half

------------------------------------------------------------------------
-- Arithmetic lemmas for bound equations
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

-- Helper: x - (y + z) ≡ (x - y) - z
-- Proof: x - (y + z) = x + (-(y + z)) = x + ((-y) + (-z)) = (x + (-y)) + (-z) = (x - y) - z
x-[y+z]≡x-y-z : ∀ x y z → x ℚP.- (y ℚ.+ z) ≡ (x ℚP.- y) ℚP.- z
x-[y+z]≡x-y-z x y z =
  cong (x ℚ.+_) (ℚP.-Distr y z)  -- x + (-(y+z)) = x + ((-y) + (-z))
  ∙ ℚP.+Assoc x (ℚP.- y) (ℚP.- z)  -- = (x + (-y)) + (-z) = (x - y) - z

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

-- Convert coherence from modified B (∼[2ε]) to standard (∼[ε])
-- Given: ∀ ε → ι a ∼[ε +₊ ε] ι a'
-- Derive: ∀ ε → ι a ∼[ε] ι a' (by using ε/2)
B→std-close : (a a' : 𝕀sd) → (∀ ε → 𝕀sd-B a a' ε) → (∀ ε → ι a ∼[ ε ] ι a')
B→std-close a a' allClose ε = subst (λ x → ι a ∼[ x ] ι a') (/2₊+/2₊≡ε₊ ε) (allClose (/2₊ ε))

ℝ→𝕀sd-Rec : Recℝ 𝕀sd 𝕀sd-B
Recℝ.ratA ℝ→𝕀sd-Rec q = SQ.[ rational→stream q ]

-- limA: use the coinductive limit lifted to 𝕀sd
-- The coherence argument has type: ∀ δ ε → B (streams δ) (streams ε) (δ +₊ ε)
-- i.e., ∀ δ ε → ι (streams δ) ∼[(δ +₊ ε) +₊ (δ +₊ ε)] ι (streams ε)
-- This matches exactly what limA-𝕀sd expects.
Recℝ.limA ℝ→𝕀sd-Rec streams coherence = limA-𝕀sd streams coherence

Recℝ.eqA ℝ→𝕀sd-Rec a a' allClose = ι-inj a a' (eqℝ (ι a) (ι a') (B→std-close a a' allClose))
  -- Given: allClose : ∀ ε → B a a' ε = ∀ ε → ι a ∼[ε +₊ ε] ι a'
  -- By B→std-close: ∀ ε → ι a ∼[ε] ι a'
  -- By eqℝ, this gives a path ι a ≡ ι a' in ℝ
  -- By ι-inj, we get a ≡ a' in 𝕀sd

-- Coherence for B relation (B a a' ε = ι a ∼[2ε] ι a')
-- rat-rat-B: close rationals produce 2ε-close stream embeddings
--
-- We need: B (ratA q) (ratA r) ε = ι (ratA q) ∼[ε +₊ ε] ι (ratA r)
--        = stream→ℝ (rational→stream q) ∼[2ε] stream→ℝ (rational→stream r)
--
-- By round-trip-clamped:
-- LHS ≡ rat (clamp q), RHS ≡ rat (clamp r)
-- So we need: rat (clamp q) ∼[2ε] rat (clamp r)
-- i.e., |clamp q - clamp r| < 2ε
--
-- We're given: |q - r| < ε
-- By clamp-lip: |clamp q - clamp r| ≤ |q - r| < ε < 2ε
Recℝ.rat-rat-B ℝ→𝕀sd-Rec q r ε vₗ vᵤ =
  subst2 (λ x y → x ∼[ ε +₊ ε ] y) (sym (round-trip-clamped q)) (sym (round-trip-clamped r))
         (rat-rat-fromAbs (clampℚ q) (clampℚ r) (ε +₊ ε) clamped-bound-2ε)
  where
    -- vₗ, vᵤ give |q - r| < ε (as in abs-bound before)

    x = q ℚP.- r
    ε' = fst ε

    -- neg-flip: -ε < x implies -x < ε
    -- Proof: By minus-<, from -e < a we get -a < -(-e), then use -Invol to get -a < e
    neg-x<ε : (ℚP.- x) ℚO.< ε'
    neg-x<ε = neg-flip x ε' vₗ
      where
        neg-flip : (a e : ℚ.ℚ) → (ℚP.- e) ℚO.< a → (ℚP.- a) ℚO.< e
        neg-flip a e proof = subst ((ℚP.- a) ℚO.<_) (ℚP.-Invol e) (minus-< (ℚP.- e) a proof)

    max<→ : (a b c : ℚ.ℚ) → a ℚO.< c → b ℚO.< c → ℚP.max a b ℚO.< c
    max<→ a b c a<c b<c = PT.rec (ℚO.isProp< (ℚP.max a b) c) handle (ℚO.isTotal≤ a b)
      where
        handle : (a ℚO.≤ b) ⊎ (b ℚO.≤ a) → ℚP.max a b ℚO.< c
        handle (inl a≤b) = subst (ℚO._< c) (sym (ℚO.≤→max a b a≤b)) b<c
        handle (inr b≤a) = subst (ℚO._< c) (sym (ℚP.maxComm a b ∙ ℚO.≤→max b a b≤a)) a<c

    abs-bound : ℚP.abs x ℚO.< ε'
    abs-bound = max<→ x (ℚP.- x) ε' vᵤ neg-x<ε

    clamped-bound : ℚP.abs (clampℚ q ℚP.- clampℚ r) ℚO.< ε'
    clamped-bound = ℚO.isTrans≤< _ _ _ (clamp-lip q r) abs-bound

    -- ε < 2ε for positive ε, so |clamp q - clamp r| < ε < 2ε
    -- Use <-o+: 0 < ε' implies ε' + 0 < ε' + ε'
    -- By +IdR: ε' + 0 ≡ ε', so we get ε' < ε' + ε' = 2ε'
    ε<2ε : ε' ℚO.< fst (ε +₊ ε)
    ε<2ε = subst (ℚO._< (ε' ℚ.+ ε')) (ℚP.+IdR ε')
                 (ℚO.<-o+ 0ℚ ε' ε' (0<ℚ₊ ε))

    clamped-bound-2ε : ℚP.abs (clampℚ q ℚP.- clampℚ r) ℚO.< fst (ε +₊ ε)
    clamped-bound-2ε = ℚO.isTrans< _ _ _ clamped-bound ε<2ε

-- rat-lim-B: With B relation, show ι (ratA q) ∼[2ε] ι (limA y p)
--
-- Given: ih : B (ratA q) (y δ) (ε - δ) = ι (ratA q) ∼[2(ε-δ)] ι (y δ)
-- By limA-𝕀sd-close: ι (limA-𝕀sd y coh-std) ∼[2δ] ι (y δ)
-- By sym∼: ι (y δ) ∼[2δ] ι (limA-𝕀sd y coh-std)
-- By triangle∼: ι (ratA q) ∼[2(ε-δ) + 2δ] ι (limA-𝕀sd y coh-std) = ∼[2ε]
Recℝ.rat-lim-B ℝ→𝕀sd-Rec q y ε p δ v ih =
  subst (λ x → ι (SQ.[ rational→stream q ]) ∼[ x ] ι (limA-𝕀sd y p))
        bound-eq
        (triangle∼ ih lim-close-sym)
  where
    -- limA-𝕀sd-close gives: ι (limA-𝕀sd y p) ∼[2δ] ι (y δ)
    lim-close : ι (limA-𝕀sd y p) ∼[ δ +₊ δ ] ι (y δ)
    lim-close = limA-𝕀sd-close y p δ

    -- By symmetry: ι (y δ) ∼[2δ] ι (limA-𝕀sd y p)
    lim-close-sym : ι (y δ) ∼[ δ +₊ δ ] ι (limA-𝕀sd y p)
    lim-close-sym = sym∼ _ _ _ lim-close

    -- The precision bound equation: (ε-δ) + (ε-δ) + δ + δ = ε + ε
    -- Actually need: ((ε-δ) + (ε-δ)) + (δ + δ) = ε + ε
    -- Let's denote ε-δ as (fst ε - fst δ, v), so the bound is (ε-δ) +₊ (ε-δ)
    εmδ : ℚ₊
    εmδ = (fst ε ℚP.- fst δ , v)

    bound-eq : (εmδ +₊ εmδ) +₊ (δ +₊ δ) ≡ ε +₊ ε
    bound-eq = ℚO.ℚ₊≡ (bound-2[e-d]+2d≡2e (fst ε) (fst δ))

-- lim-rat-B: Symmetric to rat-lim-B
Recℝ.lim-rat-B ℝ→𝕀sd-Rec x r ε δ p v ih =
  subst (λ z → ι (limA-𝕀sd x p) ∼[ z ] ι (SQ.[ rational→stream r ]))
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

-- lim-lim-B: Chain two limit closeness proofs
Recℝ.lim-lim-B ℝ→𝕀sd-Rec x y ε δ η p p' v ih =
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

    -- Convert e - (d + h) to (e - d) - h for the lemma
    εmδη≡ε-δ-η : fst εmδη ≡ (fst ε ℚP.- fst δ) ℚP.- fst η
    εmδη≡ε-δ-η = x-[y+z]≡x-y-z (fst ε) (fst δ) (fst η)

    bound-eq : ((δ +₊ δ) +₊ (εmδη +₊ εmδη)) +₊ (η +₊ η) ≡ ε +₊ ε
    bound-eq = ℚO.ℚ₊≡ (
      -- First convert εmδη to the (e - d) - h form
      cong (λ z → ((fst δ ℚ.+ fst δ) ℚ.+ (z ℚ.+ z)) ℚ.+ (fst η ℚ.+ fst η)) εmδη≡ε-δ-η
      -- Then apply the main lemma
      ∙ bound-2d+2[e-d-h]+2h≡2e (fst ε) (fst δ) (fst η))

-- isPropB: closeness is a proposition
-- Note: B a a' ε = ι a ∼[ε +₊ ε] ι a', so we use precision ε +₊ ε
Recℝ.isPropB ℝ→𝕀sd-Rec a a' ε = isProp∼ (ι a) (ι a') (ε +₊ ε)

------------------------------------------------------------------------
-- The main embedding function
------------------------------------------------------------------------

ℝ→𝕀sd-direct : ℝ → 𝕀sd
ℝ→𝕀sd-direct = Recℝ.go ℝ→𝕀sd-Rec

-- The main embedding: ι⁻¹ : ℝ → 𝕀sd
-- Embedding from HoTT Cauchy reals to signed-digit reals
-- Using the Recℝ eliminator (ℝ→𝕀sd-direct) for proper handling of eqℝ
ι⁻¹ : ℝ → 𝕀sd
ι⁻¹ = ℝ→𝕀sd-direct

------------------------------------------------------------------------
-- Full Equivalence (ℝ → ℝsd)
------------------------------------------------------------------------

-- Helper to lift (k, s) to ℝsd respecting equivalence
lift-to-ℝsd : ℤ → 𝕀sd → ℝsd
lift-to-ℝsd k = SQ.rec isSetℝsd (λ s → SQ.[ (k , s) ]) coh
  where
    coh : (s t : 𝟛ᴺ) → s ≈sd t → SQ.[ (k , s) ] ≡ SQ.[ (k , t) ]
    coh s t h = SQ.eq/ (k , s) (k , t) path
      where
        -- s ≈sd t means stream→ℝ s ≡ stream→ℝ t
        -- ≈ext means 2^k * stream→ℝ s ≡ 2^k * stream→ℝ t
        path : toℝ-raw (k , s) ≡ toℝ-raw (k , t)
        path = cong (λ x → rat (pow2ℤ k) ·ᵣ x) h

-- Full encoding: use choose-k to get exponent and normalized value,
-- then embed the normalized value using ι⁻¹.
fromℝ : ℝ → ℝsd
fromℝ x with choose-k x
... | (k , z) = lift-to-ℝsd k (ι⁻¹ (val z))

------------------------------------------------------------------------
-- Round-trip properties (postulated)
------------------------------------------------------------------------

-- The round-trip proofs require proper implementations of δ (digit
-- extraction) and choose-k (normalization).
--
-- Proof sketch for toℝ-fromℝ:
--   toℝ (fromℝ y)
--     = toℝ [ (k , δ z) ]              where (k, z) = choose-k y
--     = rat (pow2ℤ k) ·ᵣ stream→ℝ (δ z)
--     = rat (pow2ℤ k) ·ᵣ val z         by δ-correct z
--     = y                               by choose-k-correct y
--
-- Proof sketch for fromℝ-toℝ:
--   For x = [ (k, s) ], need fromℝ (toℝ [ (k, s) ]) ≡ [ (k, s) ]
--   This follows from the quotient structure: since _≈ext_ is the kernel
--   of toℝ-raw, any two ℝsd-raw codes mapping to the same ℝ are identified.

postulate
  -- TODO: Requires δ-correct and choose-k-correct
  toℝ-fromℝ : (y : ℝ) → toℝ (fromℝ y) ≡ y
  -- TODO: Follows from quotient structure once δ and choose-k are proper
  fromℝ-toℝ : (x : ℝsd) → fromℝ (toℝ x) ≡ x

------------------------------------------------------------------------
-- Type equivalence
------------------------------------------------------------------------

ℝsd≃ℝ : ℝsd ≃ ℝ
ℝsd≃ℝ = isoToEquiv (iso toℝ fromℝ toℝ-fromℝ fromℝ-toℝ)

ℝsd≡ℝ : ℝsd ≡ ℝ
ℝsd≡ℝ = ua ℝsd≃ℝ
