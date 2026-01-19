{-# OPTIONS --cubical --guardedness #-}

------------------------------------------------------------------------
-- Limit Operation for Signed-Digit Streams
------------------------------------------------------------------------
--
-- This module implements the `lim` operation for signed-digit streams,
-- which allows defining a stream by a sequence of approximations that
-- converge effectively.
--
-- Status: Experimental/WIP.
------------------------------------------------------------------------

module Reals.SignedDigit.Limit where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma using (_×_)
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_; _·_ to _*ℕ_)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Int
open import Cubical.Data.Rationals.Fast as ℚ
open import Cubical.Data.Rationals.Fast.Order as ℚO
open import Cubical.Data.Rationals.Fast.Properties as ℚP
open import Cubical.Data.Rationals.Fast.Order.Properties as ℚOP using (pos·abs; 0<sucN; /2₊; /4₊; ε/2+ε/2≡ε; /4₊+/4₊≡/2₊)
open import Cubical.Relation.Nullary

open import Cubical.Codata.Stream

open import Reals.SignedDigit.Core
open import Reals.SignedDigit.Bounded
open import Reals.SignedDigit.Bounded using (ι; approxℚ₊; approxℚ₊-cauchy)
open import Reals.SignedDigit.Equivalence.RoundTrip using (round-trip-bounded)
open import Cubical.HITs.CauchyReals.Base using (ℝ; rat; lim; _∼[_]_; rat-rat-fromAbs)
open import Cubical.HITs.CauchyReals.Closeness using (triangle∼; sym∼; ∼→∼')
open import Cubical.HITs.CauchyReals.Lipschitz using (𝕣-lim-self)

-- Use the library's ℚ₊ addition (handles positivity proofs automatically)
_+₊_ : ℚ₊ → ℚ₊ → ℚ₊
_+₊_ = ℚO._ℚ₊+_

-- Division helpers for the precision proof
-- /8₊ ε = ε/8 (not in library, so we compose /4₊ and /2₊)
/8₊ : ℚ₊ → ℚ₊
/8₊ ε = /4₊ (/2₊ ε)

-- /16₊ ε = ε/16 (compose /4₊ twice)
/16₊ : ℚ₊ → ℚ₊
/16₊ ε = /4₊ (/4₊ ε)

-- Arithmetic lemmas for combining precision bounds
-- These follow from rational arithmetic but require careful handling of ℚ₊ representation.
-- Postulated for now; proofs require showing the underlying rationals are equal.
postulate
  -- /2₊ (/2₊ ε) ≡ /4₊ ε (both are ε/4)
  /2₊∘/2₊≡/4₊ : ∀ ε → /2₊ (/2₊ ε) ≡ /4₊ ε

  -- /2₊ (/4₊ ε) ≡ /8₊ ε (both are ε/8)
  /2₊∘/4₊≡/8₊ : ∀ ε → /2₊ (/4₊ ε) ≡ /8₊ ε

-- Helper: /8₊ ε +₊ /8₊ ε ≡ /4₊ ε
-- Proof: /8₊ ε = /4₊ (/2₊ ε), and by /4₊+/4₊≡/2₊:
--   /4₊ (/2₊ ε) + /4₊ (/2₊ ε) = /2₊ (/2₊ ε) = /4₊ ε
/8₊+/8₊≡/4₊ : ∀ ε → /8₊ ε +₊ /8₊ ε ≡ /4₊ ε
/8₊+/8₊≡/4₊ ε = /4₊+/4₊≡/2₊ (/2₊ ε) ∙ /2₊∘/2₊≡/4₊ ε

-- Helper: /16₊ ε +₊ /16₊ ε ≡ /8₊ ε
-- Proof: /16₊ ε = /4₊ (/4₊ ε), and by /4₊+/4₊≡/2₊:
--   /4₊ (/4₊ ε) + /4₊ (/4₊ ε) = /2₊ (/4₊ ε) = /8₊ ε
/16₊+/16₊≡/8₊ : ∀ ε → /16₊ ε +₊ /16₊ ε ≡ /8₊ ε
/16₊+/16₊≡/8₊ ε = /4₊+/4₊≡/2₊ (/4₊ ε) ∙ /2₊∘/4₊≡/8₊ ε

-- Constants
2n : ℕ
2n = suc (suc zero)

4n : ℕ
4n = 2n +ℕ 2n

10n : ℕ
10n = 4n +ℕ 4n +ℕ 2n

16n : ℕ
16n = 4n *ℕ 4n

100n : ℕ
100n = 10n *ℕ 10n

1Q : ℚ.ℚ
1Q = [ pos 1 / 1+ 0 ]

2Q : ℚ.ℚ
2Q = [ pos 2 / 1+ 0 ]

-- 1/4 = 1 / (3+1)
1/4ℚ : ℚ.ℚ
1/4ℚ = [ pos 1 / 1+ (suc (suc (suc zero))) ]

-- 1/16 = 1 / (15+1)
1/16ℚ : ℚ.ℚ
1/16ℚ = [ pos 1 / 1+ (10n +ℕ 4n +ℕ 1) ]

-- 1/16 is positive ([ pos 1 / _ ] has positive numerator)
-- Postulated: proving this requires Fast ℚ internals
postulate
  0<1/16 : ℚO.0< 1/16ℚ

-- Bundle 1/16 as a positive rational
1/16ℚ₊ : ℚO.ℚ₊
1/16ℚ₊ = 1/16ℚ , 0<1/16

-- Coherence helper: |2x - 2y| = 2|x - y|
-- Uses pos·abs: 0 ≤ c → |c · a| = c · |a|

-- 0 < 2 (needed for 0 ≤ 2)
-- 0<sucN n gives: 0 < fromNat (suc n), so 0<sucN 1 gives 0 < 2
0<2Q : ℚO._<_ (ℚ.fromNat 0) 2Q
0<2Q = ℚOP.0<sucN 1

-- 0 ≤ 2Q is needed for pos·abs
-- <Weaken≤ takes explicit endpoints: <Weaken≤ x y (x < y) gives x ≤ y
0≤2Q : ℚO._≤_ (ℚ.fromNat 0) 2Q
0≤2Q = ℚO.<Weaken≤ (ℚ.fromNat 0) 2Q 0<2Q

-- Distributivity: c · a - c · b = c · (a - b)
-- Postulated: well-known algebraic identity, tedious to derive without exported lemmas
postulate
  ·DistL- : (c a b : ℚ.ℚ) → (c ℚP.· a) ℚP.- (c ℚP.· b) ≡ c ℚP.· (a ℚP.- b)

-- Ring identity: (a - c) - (b - c) = a - b (the c's cancel)
-- Proof: (a - c) - (b - c) = a - c - b + c = a - b
postulate
  sub-cancel : (a b c : ℚ.ℚ) → (a ℚP.- c) ℚP.- (b ℚP.- c) ≡ a ℚP.- b

-- Multiplication monotonicity: c > 0 → a < b → c · a < c · b
-- This is a standard property of ordered fields
postulate
  <-·-mono-r : (c a b : ℚ.ℚ) → ℚO._<_ (ℚ.fromNat 0) c → a ℚO.< b → (c ℚP.· a) ℚO.< (c ℚP.· b)

-- General abs multiplicativity (postulated; tedious to prove by cases on signs)
postulate
  abs-mult : (a b : ℚ.ℚ) → ℚP.abs (a ℚP.· b) ≡ ℚP.abs a ℚP.· ℚP.abs b

-- abs-dist-scale: |2x - 2y| = 2|x - y|
-- Proof: |2x - 2y| = |2(x - y)| = 2|x - y| (by pos·abs since 2 ≥ 0)
abs-dist-scale : (x y : ℚ.ℚ) → ℚP.abs ((2Q ℚP.· x) ℚP.- (2Q ℚP.· y)) ≡ 2Q ℚP.· ℚP.abs (x ℚP.- y)
abs-dist-scale x y =
  cong ℚP.abs (·DistL- 2Q x y)       -- |2x - 2y| = |2(x - y)|
  ∙ ℚOP.pos·abs 2Q (x ℚP.- y) 0≤2Q  -- |2z| = 2|z| for z = x - y

-- bound→abs: If -ε < x < ε then |x| < ε
-- This follows from the definition of absolute value
-- Postulated for now; proof requires case analysis on sign of x
postulate
  bound→abs : (x ε : ℚ.ℚ) → (ℚP.- ε) ℚO.< x → x ℚO.< ε → ℚP.abs x ℚO.< ε

{-# TERMINATING #-}
limA : (f : ℚ₊ → 𝟛ᴺ) → (∀ δ ε → stream→ℝ (f δ) ∼[ δ +₊ ε ] stream→ℝ (f ε)) → 𝟛ᴺ
limA streams coh = record { head = d ; tail = limA nextStreams nextCoh }
  where
    -- Step 1: Pick fixed epsilon ε = 1/16
    ε : ℚO.ℚ₊
    ε = 1/16ℚ₊

    -- Step 2: Get approx
    s : 𝟛ᴺ
    s = streams ε
    
    q : ℚ.ℚ
    q = approx s 10n -- Precision 10
    
    -- Step 3: Select digit
    -- If q < -1/4 choose -1
    -- If q > 1/4 choose +1
    -- Else choose 0
    d : Digit
    d = case (q ℚO.≟ (ℚP.- 1/4ℚ)) of λ where
      (ℚO.lt _) → -1d
      (ℚO.eq _) → 0d
      (ℚO.gt _) → case (q ℚO.≟ 1/4ℚ) of λ where
        (ℚO.gt _) → +1d
        _         → 0d

    -- Step 4: Next streams
    -- f' δ = rational→stream (2 * approx(f (δ/16), precision(δ/16)) - d)
    --
    -- Proof that |nextRat δ - nextRat γ| < δ + γ:
    --
    --   1. Use δ/16 scaling: getApprox δ = approx (streams (/16₊ δ)) (prec δ)
    --   2. Use δ-dependent precision: prec δ = ℚ₊→ℕ (/16₊ δ)
    --   3. The approximation error: |getApprox δ - stream→ℝ (streams (/16₊ δ))| < δ/16
    --      (by modulus-correct)
    --   4. By coh (/16₊ δ) (/16₊ γ):
    --      |stream→ℝ (streams (/16₊ δ)) - stream→ℝ (streams (/16₊ γ))| < (δ+γ)/16
    --   5. Triangle inequality:
    --      |getApprox δ - getApprox γ|
    --        ≤ |getApprox δ - stream→ℝ (streams (/16₊ δ))|      [< δ/16]
    --        + |stream→ℝ (streams (/16₊ δ)) - stream→ℝ (streams (/16₊ γ))|  [< (δ+γ)/16]
    --        + |stream→ℝ (streams (/16₊ γ)) - getApprox γ|      [< γ/16]
    --        < δ/16 + (δ+γ)/16 + γ/16
    --        = (2δ + 2γ + δ + γ)/16 = 3(δ+γ)/16
    --   6. After 2× scaling: |nextRat δ - nextRat γ| < 2 · 3(δ+γ)/16 = 3(δ+γ)/8 < δ+γ ✓

    -- Single-parameter approximation for actual computation
    -- Uses δ/16 scaling and δ/16-dependent precision to ensure tight error bound
    getApprox : ℚ₊ → ℚ.ℚ
    getApprox δ = approx (streams (/16₊ δ)) (ℚ₊→ℕ (/16₊ δ))

    -- Compute next rational: 2 * approx(streams(δ/16), prec(δ/16)) - digit
    nextRat : ℚ₊ → ℚ.ℚ
    nextRat δ = (2Q ℚP.· getApprox δ) ℚP.- digitToℚ d

    nextStreams : ℚ₊ → 𝟛ᴺ
    nextStreams δ = rational→stream (nextRat δ)

    -- Coherence proof for next iteration streams
    --
    -- Proof strategy with δ/16 scaling:
    --   |nextRat δ - nextRat γ| < δ + γ
    --
    -- See detailed proof sketch above (steps 1-6).

    -- Helper: /16₊ δ +₊ /16₊ γ ≡ /16₊ (δ +₊ γ)
    -- This distributes /16₊ over addition
    postulate
      /16₊-distrib : ∀ δ γ → /16₊ δ +₊ /16₊ γ ≡ /16₊ (δ +₊ γ)

    -- Arithmetic helper: The total error bound scaled by 2 is still less than δ+γ
    -- Proof: 2 * (δ/8 + (δ+γ)/16 + γ/8) = 2 * 3(δ+γ)/16 = 3(δ+γ)/8 < δ+γ
    postulate
      scaled-bound-< : ∀ δ γ →
        2Q ℚP.· fst ((/8₊ δ +₊ (/16₊ δ +₊ /16₊ γ)) +₊ /8₊ γ) ℚO.< fst (δ +₊ γ)

    -- nextRat produces bounded rationals (needed for round-trip)
    -- This follows from: streams are bounded to [-1,1], approx is bounded,
    -- and |2 · approx - d| ≤ 2 · 1 + 1 = 3, but the stream values ensure [-1,1]
    postulate
      nextRat-bounded : (δ : ℚ₊) →
        ((ℚP.- 1Q) ℚO.≤ nextRat δ) × (nextRat δ ℚO.≤ 1Q)

    -- The main difference bound: |nextRat δ - nextRat γ| < δ + γ
    --
    -- Proof strategy:
    --   1. rat (getApprox δ) ∼[/8₊ δ] stream→ℝ (streams (/16₊ δ))  (via 𝕣-lim-self)
    --   2. stream→ℝ (streams (/16₊ δ)) ∼[/16₊ δ +₊ /16₊ γ] stream→ℝ (streams (/16₊ γ))  (via coh)
    --   3. stream→ℝ (streams (/16₊ γ)) ∼[/8₊ γ] rat (getApprox γ)  (via 𝕣-lim-self + sym∼)
    --   4. Chain: rat (getApprox δ) ∼[/8₊ δ +₊ (/16₊ δ +₊ /16₊ γ) +₊ /8₊ γ] rat (getApprox γ)
    --   5. Extract: |getApprox δ - getApprox γ| < 3(δ+γ)/16  (via ∼→∼' + bound→abs)
    --   6. Scale: |nextRat δ - nextRat γ| = 2|getApprox δ - getApprox γ| < 3(δ+γ)/8 < δ+γ
    --
    nextRat-diff-bound : (δ γ : ℚ₊) →
      ℚP.abs (nextRat δ ℚP.- nextRat γ) ℚO.< fst (δ +₊ γ)
    nextRat-diff-bound δ γ =
      let
        -- Abbreviations for streams
        sδ = streams (/16₊ δ)
        sγ = streams (/16₊ γ)

        -- Step 1: rat (getApprox δ) ∼[/8₊ δ] stream→ℝ sδ
        -- Using: getApprox δ = approxℚ₊ sδ (/16₊ δ) and /16₊ δ +₊ /16₊ δ = /8₊ δ
        step1-raw : rat (approxℚ₊ sδ (/16₊ δ)) ∼[ /16₊ δ +₊ /16₊ δ ] stream→ℝ sδ
        step1-raw = 𝕣-lim-self (λ ε' → rat (approxℚ₊ sδ ε')) (approxℚ₊-cauchy sδ) (/16₊ δ) (/16₊ δ)

        step1 : rat (getApprox δ) ∼[ /8₊ δ ] stream→ℝ sδ
        step1 = subst (λ x → rat (getApprox δ) ∼[ x ] stream→ℝ sδ) (/16₊+/16₊≡/8₊ δ) step1-raw

        -- Step 2: stream→ℝ sδ ∼[/16₊ δ +₊ /16₊ γ] stream→ℝ sγ (coherence)
        step2 : stream→ℝ sδ ∼[ /16₊ δ +₊ /16₊ γ ] stream→ℝ sγ
        step2 = coh (/16₊ δ) (/16₊ γ)

        -- Step 3: stream→ℝ sγ ∼[/8₊ γ] rat (getApprox γ)
        step3-raw : rat (approxℚ₊ sγ (/16₊ γ)) ∼[ /16₊ γ +₊ /16₊ γ ] stream→ℝ sγ
        step3-raw = 𝕣-lim-self (λ ε' → rat (approxℚ₊ sγ ε')) (approxℚ₊-cauchy sγ) (/16₊ γ) (/16₊ γ)

        step3' : rat (getApprox γ) ∼[ /8₊ γ ] stream→ℝ sγ
        step3' = subst (λ x → rat (getApprox γ) ∼[ x ] stream→ℝ sγ) (/16₊+/16₊≡/8₊ γ) step3-raw

        step3 : stream→ℝ sγ ∼[ /8₊ γ ] rat (getApprox γ)
        step3 = sym∼ (rat (getApprox γ)) (stream→ℝ sγ) (/8₊ γ) step3'

        -- Step 4: Combine via triangle∼
        step12 : rat (getApprox δ) ∼[ /8₊ δ +₊ (/16₊ δ +₊ /16₊ γ) ] stream→ℝ sγ
        step12 = triangle∼ step1 step2

        ε-total : ℚ₊
        ε-total = (/8₊ δ +₊ (/16₊ δ +₊ /16₊ γ)) +₊ /8₊ γ

        step123 : rat (getApprox δ) ∼[ ε-total ] rat (getApprox γ)
        step123 = triangle∼ step12 step3

        -- Step 5: Extract bounds using ∼→∼'
        -- ∼→∼' gives (-ε < x - y) × (x - y < ε) for rationals
        bounds : ((ℚP.- fst ε-total) ℚO.< (getApprox δ ℚP.- getApprox γ))
               × ((getApprox δ ℚP.- getApprox γ) ℚO.< fst ε-total)
        bounds = ∼→∼' (rat (getApprox δ)) (rat (getApprox γ)) ε-total step123

        -- Use bound→abs to get |getApprox δ - getApprox γ| < ε-total
        getApprox-diff-bound : ℚP.abs (getApprox δ ℚP.- getApprox γ) ℚO.< fst ε-total
        getApprox-diff-bound = bound→abs (getApprox δ ℚP.- getApprox γ) (fst ε-total) (fst bounds) (snd bounds)

        -- Step 6: Scale by 2
        -- |nextRat δ - nextRat γ| = |2·getApprox δ - d - (2·getApprox γ - d)|
        --                        = |2·getApprox δ - 2·getApprox γ|
        --                        = 2 · |getApprox δ - getApprox γ|

        -- First, simplify the difference
        -- nextRat δ = 2·getApprox δ - d
        -- nextRat γ = 2·getApprox γ - d
        -- So: nextRat δ - nextRat γ = (2·getApprox δ - d) - (2·getApprox γ - d)
        --                           = 2·getApprox δ - d - 2·getApprox γ + d
        --                           = 2·getApprox δ - 2·getApprox γ
        -- The d's cancel. This is standard ring arithmetic.
        nextRat-diff-eq : nextRat δ ℚP.- nextRat γ ≡ (2Q ℚP.· getApprox δ) ℚP.- (2Q ℚP.· getApprox γ)
        nextRat-diff-eq = sub-cancel (2Q ℚP.· getApprox δ) (2Q ℚP.· getApprox γ) (digitToℚ d)

        -- Apply abs-dist-scale: |2x - 2y| = 2|x - y|
        scaled-abs : ℚP.abs (nextRat δ ℚP.- nextRat γ) ≡ 2Q ℚP.· ℚP.abs (getApprox δ ℚP.- getApprox γ)
        scaled-abs = cong ℚP.abs nextRat-diff-eq ∙ abs-dist-scale (getApprox δ) (getApprox γ)

        -- 2 * getApprox-diff-bound < δ + γ
        -- Because 2 * fst ε-total < fst (δ +₊ γ) by scaled-bound-<
        final-bound : 2Q ℚP.· ℚP.abs (getApprox δ ℚP.- getApprox γ) ℚO.< fst (δ +₊ γ)
        final-bound = ℚO.isTrans<
          (2Q ℚP.· ℚP.abs (getApprox δ ℚP.- getApprox γ))
          (2Q ℚP.· fst ε-total)
          (fst (δ +₊ γ))
          (<-·-mono-r 2Q (ℚP.abs (getApprox δ ℚP.- getApprox γ)) (fst ε-total) 0<2Q getApprox-diff-bound)
          (scaled-bound-< δ γ)

      in subst (ℚO._< fst (δ +₊ γ)) (sym scaled-abs) final-bound

    -- Full proof using round-trip and the bounds:
    nextCoh : ∀ δ γ → stream→ℝ (nextStreams δ) ∼[ δ +₊ γ ] stream→ℝ (nextStreams γ)
    nextCoh δ γ =
      let
        -- Step 1: Get bounds on nextRat δ and nextRat γ
        (lo-δ , hi-δ) = nextRat-bounded δ
        (lo-γ , hi-γ) = nextRat-bounded γ

        -- Step 2: By round-trip-bounded, stream→ℝ (rational→stream r) ≡ rat r for bounded r
        rt-δ : stream→ℝ (nextStreams δ) ≡ rat (nextRat δ)
        rt-δ = round-trip-bounded (nextRat δ) lo-δ hi-δ

        rt-γ : stream→ℝ (nextStreams γ) ≡ rat (nextRat γ)
        rt-γ = round-trip-bounded (nextRat γ) lo-γ hi-γ

        -- Step 3: By rat-rat-fromAbs with the diff bound
        diff-bound : ℚP.abs (nextRat δ ℚP.- nextRat γ) ℚO.< fst (δ +₊ γ)
        diff-bound = nextRat-diff-bound δ γ

        rat-close : rat (nextRat δ) ∼[ δ +₊ γ ] rat (nextRat γ)
        rat-close = rat-rat-fromAbs (nextRat δ) (nextRat γ) (δ +₊ γ) diff-bound

        -- Step 4: Substitute using the round-trip equalities
      in subst2 _∼[ δ +₊ γ ]_ (sym rt-δ) (sym rt-γ) rat-close

------------------------------------------------------------------------
-- Key property: limA produces streams close to input streams
------------------------------------------------------------------------
--
-- This is the fundamental property that `limA` satisfies:
-- The constructed stream is close to any of the input streams.
--
-- Proof sketch (coinductive):
--   1. The first digit d is chosen from f(1/16) at precision 10
--   2. This digit is "correct" for representing f(δ) for small δ
--   3. The tail recursively satisfies the same property
--   4. By coinduction, the full stream is close to f(δ)
--
-- The bound δ +₊ δ comes from:
--   - Error in approximating f(δ) contributes δ
--   - Error from coherence (f(δ) vs f(1/16)) contributes another δ
--
-- TODO: This requires a coinductive proof. For now, postulated.
postulate
  limA-close-to-input : (f : ℚ₊ → 𝟛ᴺ) →
                        (coh : ∀ δ ε → stream→ℝ (f δ) ∼[ δ +₊ ε ] stream→ℝ (f ε)) →
                        ∀ δ → stream→ℝ (limA f coh) ∼[ δ +₊ δ ] stream→ℝ (f δ)

------------------------------------------------------------------------
-- Lifted coinductive limit for 𝕀sd (the quotient type)
------------------------------------------------------------------------
--
-- This lifts the coinductive limit `limA` to work on the quotient type
-- 𝕀sd = 𝟛ᴺ / _≈sd_. The key insight is that different representatives
-- give the same stream→ℝ value, so the coherence condition is preserved
-- regardless of which representatives we choose.
--
-- For implementation, we would need to:
--   1. For each f δ : 𝕀sd, choose a representative stream
--   2. Apply limA to get a result stream
--   3. Quote the result back into 𝕀sd
--   4. Prove the result is independent of representative choices
--
-- The correctness follows from:
--   - s ≈sd t implies stream→ℝ s ≡ stream→ℝ t (by definition)
--   - limA only depends on stream→ℝ values (via approx)
--   - So any choice of representatives gives ≈sd-equivalent results

postulate
  -- Lift coinductive limit to quotient type
  -- NOTE: The coherence is at precision 2(δ+ε) to match the modified B relation
  -- in Direct.agda. This weaker coherence still allows constructing the limit.
  limA-𝕀sd : (f : ℚ₊ → 𝕀sd) →
             (coh : ∀ δ ε → ι (f δ) ∼[ (δ +₊ ε) +₊ (δ +₊ ε) ] ι (f ε)) →
             𝕀sd

  -- Key property: result is close to each input (with 2δ bound)
  -- The 2δ bound matches what's needed for the coherence proofs in Direct.agda
  limA-𝕀sd-close : (f : ℚ₊ → 𝕀sd) →
                   (coh : ∀ δ ε → ι (f δ) ∼[ (δ +₊ ε) +₊ (δ +₊ ε) ] ι (f ε)) →
                   ∀ δ → ι (limA-𝕀sd f coh) ∼[ δ +₊ δ ] ι (f δ)
