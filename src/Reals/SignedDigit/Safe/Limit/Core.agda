{-# OPTIONS --cubical --safe --guardedness #-}

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

module Reals.SignedDigit.Safe.Limit.Core where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma using (_×_; Σ; Σ-syntax)
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_; _·_ to _*ℕ_)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Int
open import Cubical.Data.Rationals.Fast as ℚ
open import Cubical.Data.Rationals.Fast.Order as ℚO
open import Cubical.Data.Rationals.Fast.Properties as ℚP
open import Cubical.Data.Rationals.Fast.Order.Properties as ℚOP using (pos·abs; 0<sucN; /2₊; /4₊; ε/2+ε/2≡ε; /4₊+/4₊≡/2₊; /4₊≡/2₊/2₊; 0<pos; abs·abs; decℚ<?)
open import Cubical.Data.Rationals.Fast.Order as ℚO using (ℚ₊; ℚ₊≡; _≟_; lt; eq; gt; _<_; _≤_; 0<_; <Weaken≤; isTrans<; <-·o; absFrom<×<; <→0<; 0<→<; <-o+; 0<ℚ₊)
open import Cubical.Relation.Nullary
open import Cubical.Tactics.CommRingSolverFast.FastRationalsReflection using (ℚ!!)

open import Cubical.Codata.Stream

open import Reals.SignedDigit.Safe.Core
open import Reals.SignedDigit.Safe.Bounded
open import Reals.SignedDigit.Safe.Bounded using (approxℚ₊; approxℚ₊-cauchy)
open import Reals.SignedDigit.Safe.Equivalence.RoundTrip using (round-trip-bounded)
open import Cubical.HITs.CauchyReals.Base using (ℝ; rat; lim; _∼[_]_; rat-rat-fromAbs; eqℝ)
open import Cubical.HITs.CauchyReals.Closeness using (triangle∼; sym∼; ∼→∼')
open import Cubical.HITs.CauchyReals.Lipschitz using (𝕣-lim-self; ∼-monotone≤)
-- 𝕣-lim-self imported via Closeness

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
-- These follow from rational arithmetic and are proven using ℚ₊≡.

-- /2₊ (/2₊ ε) ≡ /4₊ ε (both are ε/4)
-- Proof: Use /4₊≡/2₊/2₊ from the library and lift via ℚ₊≡
/2₊∘/2₊≡/4₊ : ∀ ε → /2₊ (/2₊ ε) ≡ /4₊ ε
/2₊∘/2₊≡/4₊ ε = ℚ₊≡ (sym (/4₊≡/2₊/2₊ ε))

-- /2₊ (/4₊ ε) ≡ /8₊ ε (both are ε/8)
-- Proof: /8₊ ε = /4₊ (/2₊ ε), need /2₊ (/4₊ ε) ≡ /4₊ (/2₊ ε)
-- This follows from commutativity: (ε/4)/2 = (ε/2)/4 = ε/8
/2₊∘/4₊≡/8₊ : ∀ ε → /2₊ (/4₊ ε) ≡ /8₊ ε
/2₊∘/4₊≡/8₊ ε = ℚ₊≡ ℚ!!

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
-- Uses 0<pos from the library: 0 < [ pos (suc n) / m ], then convert via <→0<
0<1/16 : ℚO.0< 1/16ℚ
0<1/16 = <→0< 1/16ℚ (ℚOP.0<pos 0 (1+ (10n +ℕ 4n +ℕ 1)))

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
-- Proof: Direct application of the ℚ!! ring solver
·DistL- : (c a b : ℚ.ℚ) → (c ℚP.· a) ℚP.- (c ℚP.· b) ≡ c ℚP.· (a ℚP.- b)
·DistL- c a b = ℚ!!

-- Ring identity: (a - c) - (b - c) = a - b (the c's cancel)
-- Proof: Direct application of the ℚ!! ring solver
sub-cancel : (a b c : ℚ.ℚ) → (a ℚP.- c) ℚP.- (b ℚP.- c) ≡ a ℚP.- b
sub-cancel a b c = ℚ!!

-- Multiplication monotonicity: c > 0 → a < b → c · a < c · b
-- Proof: Use <-·o from library with commutativity
<-·-mono-r : (c a b : ℚ.ℚ) → ℚO._<_ (ℚ.fromNat 0) c → a ℚO.< b → (c ℚP.· a) ℚO.< (c ℚP.· b)
<-·-mono-r c a b 0<c a<b = subst2 ℚO._<_ (ℚP.·Comm a c) (ℚP.·Comm b c) (<-·o a b c 0<c a<b)

-- General abs multiplicativity: |a · b| = |a| · |b|
-- Proof: Use sym of abs·abs from the library
abs-mult : (a b : ℚ.ℚ) → ℚP.abs (a ℚP.· b) ≡ ℚP.abs a ℚP.· ℚP.abs b
abs-mult a b = sym (ℚOP.abs·abs a b)

-- abs-dist-scale: |2x - 2y| = 2|x - y|
-- Proof: |2x - 2y| = |2(x - y)| = 2|x - y| (by pos·abs since 2 ≥ 0)
abs-dist-scale : (x y : ℚ.ℚ) → ℚP.abs ((2Q ℚP.· x) ℚP.- (2Q ℚP.· y)) ≡ 2Q ℚP.· ℚP.abs (x ℚP.- y)
abs-dist-scale x y =
  cong ℚP.abs (·DistL- 2Q x y)       -- |2x - 2y| = |2(x - y)|
  ∙ ℚOP.pos·abs 2Q (x ℚP.- y) 0≤2Q  -- |2z| = 2|z| for z = x - y

-- bound→abs: If -ε < x < ε then |x| < ε
-- Proof: Use absFrom<×< from the library
bound→abs : (x ε : ℚ.ℚ) → (ℚP.- ε) ℚO.< x → x ℚO.< ε → ℚP.abs x ℚO.< ε
bound→abs x ε neg-bound pos-bound = absFrom<×< ε x neg-bound pos-bound

limA-step :
  (f : ℚ₊ → 𝟛ᴺ) →
  (∀ δ ε → stream→ℝ (f δ) ∼[ δ +₊ ε ] stream→ℝ (f ε)) →
  Digit × (Σ[ nextStreams ∈ (ℚ₊ → 𝟛ᴺ) ]
    (∀ δ γ → stream→ℝ (nextStreams δ) ∼[ δ +₊ γ ] stream→ℝ (nextStreams γ)))
limA-step streams coh = d , (nextStreams , nextCoh)
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
    nextStreams δ = rational→stream (clampℚ (nextRat δ))

    -- Coherence proof for next iteration streams
    --
    -- Proof strategy with δ/16 scaling:
    --   |nextRat δ - nextRat γ| < δ + γ
    --
    -- See detailed proof sketch above (steps 1-6).

    -- Helper: /16₊ δ +₊ /16₊ γ ≡ /16₊ (δ +₊ γ)
    -- This distributes /16₊ over addition
    -- Proof: (δ/16) + (γ/16) = (δ+γ)/16, proven via ℚ₊≡ and ℚ!!
    /16₊-distrib : ∀ δ γ → /16₊ δ +₊ /16₊ γ ≡ /16₊ (δ +₊ γ)
    /16₊-distrib δ γ = ℚ₊≡ ℚ!!

    -- Arithmetic helper: The total error bound scaled by 2 is still less than δ+γ
    -- Proof: 2 * (δ/8 + δ/16 + γ/16 + γ/8) = 3(δ+γ)/8 < δ+γ (since 3/8 < 1)
    --
    -- Strategy:
    -- 1. Show LHS = (3/8) · (δ+γ) algebraically
    -- 2. Show (3/8) · x < x for x > 0 using order properties
    --
    -- The algebraic equality:
    --   2 * (δ/8 + δ/16 + γ/16 + γ/8)
    --   = 2 * ((2δ + δ + γ + 2γ)/16)
    --   = 2 * (3δ + 3γ)/16
    --   = (6δ + 6γ)/16
    --   = (3δ + 3γ)/8
    --   = (3/8) * (δ + γ)
    --
    -- For the inequality, since δ+γ > 0 and 3/8 < 1:
    --   (3/8) * (δ+γ) < 1 * (δ+γ) = δ+γ
    --
    -- Proof: 2 · (δ/8 + (δ/16 + γ/16) + γ/8) = 2 · 3(δ+γ)/16 = 3(δ+γ)/8 < δ+γ
    -- Since 3/8 < 1 and (δ+γ) > 0.
    --
    -- Strategy: Show (3/8) · (δ+γ) < 1 · (δ+γ) = δ+γ using <-·-mono-r
    -- Then substitute lhs = (3/8) · (δ+γ) via ℚ!!
    scaled-bound-< : ∀ δ γ →
      2Q ℚP.· fst ((/8₊ δ +₊ (/16₊ δ +₊ /16₊ γ)) +₊ /8₊ γ) ℚO.< fst (δ +₊ γ)
    scaled-bound-< δ γ =
      let
        lhs = 2Q ℚP.· fst ((/8₊ δ +₊ (/16₊ δ +₊ /16₊ γ)) +₊ /8₊ γ)
        δγ = fst (δ +₊ γ)

        -- 3/8 as a rational
        3/8ℚ : ℚ.ℚ
        3/8ℚ = [ pos 3 / 1+ 7 ]

        -- 5/8 as a rational
        5/8ℚ : ℚ.ℚ
        5/8ℚ = [ pos 5 / 1+ 7 ]

        -- 0 < 5/8 (5/8 is a positive rational)
        5/8-pos : 0ℚ < 5/8ℚ
        5/8-pos = ℚOP.0<pos 4 (1+ 7)

        -- 3/8 + 5/8 = 1
        sum-eq : 3/8ℚ ℚ.+ 5/8ℚ ≡ [ pos 1 / 1+ 0 ]
        sum-eq = ℚ!!

        -- 3/8 + 0 < 3/8 + 5/8  by <-o+
        step-3/8 : (3/8ℚ ℚ.+ 0ℚ) < (3/8ℚ ℚ.+ 5/8ℚ)
        step-3/8 = <-o+ 0ℚ 5/8ℚ 3/8ℚ 5/8-pos

        -- 3/8 + 0 = 3/8
        lhs-simp : 3/8ℚ ℚ.+ 0ℚ ≡ 3/8ℚ
        lhs-simp = ℚP.+IdR 3/8ℚ

        -- 3/8 < 1
        3/8<1 : 3/8ℚ < [ pos 1 / 1+ 0 ]
        3/8<1 = subst2 _<_ lhs-simp sum-eq step-3/8

        -- δ+γ > 0 from the ℚ₊ structure
        δγ-pos : 0ℚ < δγ
        δγ-pos = 0<→< δγ (snd (δ +₊ γ))

        -- (δ+γ) · (3/8) < (δ+γ) · 1 by monotonicity (<-·-mono-r gives c·a < c·b)
        scaled-ineq : (δγ ℚP.· 3/8ℚ) < (δγ ℚP.· [ pos 1 / 1+ 0 ])
        scaled-ineq = <-·-mono-r δγ 3/8ℚ [ pos 1 / 1+ 0 ] δγ-pos 3/8<1

        -- (δ+γ) · 1 = δ+γ
        one-id : δγ ℚP.· [ pos 1 / 1+ 0 ] ≡ δγ
        one-id = ℚP.·IdR δγ

        -- lhs = (δ+γ) · (3/8) algebraically (by commutativity and simplification)
        lhs-eq : lhs ≡ δγ ℚP.· 3/8ℚ
        lhs-eq = ℚ!!

        -- Chain: lhs = (δ+γ)·(3/8) < (δ+γ)·1 = δ+γ
        step1 : (δγ ℚP.· 3/8ℚ) < δγ
        step1 = subst ((δγ ℚP.· 3/8ℚ) <_) one-id scaled-ineq

      in subst (_< δγ) (sym lhs-eq) step1

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
        -- Step 1: nextStreams uses clamped rationals, which are always in [-1,1].
        lo-δ : (ℚP.- 1Q) ℚO.≤ clampℚ (nextRat δ)
        lo-δ = fst (abs≤1→interval (clampℚ (nextRat δ)) (clampℚ-bound (nextRat δ)))

        hi-δ : clampℚ (nextRat δ) ℚO.≤ 1Q
        hi-δ = snd (abs≤1→interval (clampℚ (nextRat δ)) (clampℚ-bound (nextRat δ)))

        lo-γ : (ℚP.- 1Q) ℚO.≤ clampℚ (nextRat γ)
        lo-γ = fst (abs≤1→interval (clampℚ (nextRat γ)) (clampℚ-bound (nextRat γ)))

        hi-γ : clampℚ (nextRat γ) ℚO.≤ 1Q
        hi-γ = snd (abs≤1→interval (clampℚ (nextRat γ)) (clampℚ-bound (nextRat γ)))

        -- Step 2: By round-trip-bounded, stream→ℝ (rational→stream r) ≡ rat r for bounded r
        rt-δ : stream→ℝ (nextStreams δ) ≡ rat (clampℚ (nextRat δ))
        rt-δ = round-trip-bounded (clampℚ (nextRat δ)) lo-δ hi-δ

        rt-γ : stream→ℝ (nextStreams γ) ≡ rat (clampℚ (nextRat γ))
        rt-γ = round-trip-bounded (clampℚ (nextRat γ)) lo-γ hi-γ

        -- Step 3: The clamp is 1-Lipschitz, so the clamped difference is also < δ+γ.
        diff-bound : ℚP.abs (clampℚ (nextRat δ) ℚP.- clampℚ (nextRat γ)) ℚO.< fst (δ +₊ γ)
        diff-bound = ℚO.isTrans≤< _ _ _
                      (clamp-lip (nextRat δ) (nextRat γ))
                      (nextRat-diff-bound δ γ)

        rat-close : rat (clampℚ (nextRat δ)) ∼[ δ +₊ γ ] rat (clampℚ (nextRat γ))
        rat-close = rat-rat-fromAbs (clampℚ (nextRat δ)) (clampℚ (nextRat γ)) (δ +₊ γ) diff-bound

        -- Step 4: Substitute using the round-trip equalities
      in subst2 _∼[ δ +₊ γ ]_ (sym rt-δ) (sym rt-γ) rat-close

limA : (f : ℚ₊ → 𝟛ᴺ) → (∀ δ ε → stream→ℝ (f δ) ∼[ δ +₊ ε ] stream→ℝ (f ε)) → 𝟛ᴺ
head (limA streams coh) = fst (limA-step streams coh)
tail (limA streams coh) = limA nextStreams nextCoh
  where
    step : Digit × (Σ[ nextStreams ∈ (ℚ₊ → 𝟛ᴺ) ]
      (∀ δ γ → stream→ℝ (nextStreams δ) ∼[ δ +₊ γ ] stream→ℝ (nextStreams γ)))
    step = limA-step streams coh

    nextStreams : ℚ₊ → 𝟛ᴺ
    nextStreams = fst (snd step)

    nextCoh : ∀ δ γ → stream→ℝ (nextStreams δ) ∼[ δ +₊ γ ] stream→ℝ (nextStreams γ)
    nextCoh = snd (snd step)

------------------------------------------------------------------------
-- Key property: limA produces streams close to input streams
------------------------------------------------------------------------
--
-- This is the FUNDAMENTAL property that all other limit properties depend on.
-- Once proven, limA-𝕀sd and limA-𝕀sd-close follow.
--
-- Proof approach:
-- The proof requires showing that `stream→ℝ (limA f coh)` is close to each
-- `stream→ℝ (f δ)`. This involves:
--
--   1. Show that `stream→ℝ (limA f coh) ≡ lim (stream→ℝ ∘ f) coh`
--      (the coinductive construction equals the Cauchy limit)
--
--   2. Use `𝕣-lim-self`: for any Cauchy sequence s with coherence coh,
--      `s δ ∼[δ + ε] lim s coh`
--
--   3. Combined: `stream→ℝ (limA f coh) ∼[δ + δ] stream→ℝ (f δ)`
--
-- The equality in step 1 is the core coinductive argument. It requires:
--   a. Showing the approximations of `limA f coh` converge to the same
--      value as the limit `lim (stream→ℝ ∘ f) coh`
--   b. Using `eqℝ` to convert closeness at all ε to equality
--
-- This is proven in Surjection.agda as `limA-stream-correct`, but that
-- proof USES this postulate. An independent proof would need to reason
-- directly about the coinductive structure of `limA`.
--
-- The bound δ +₊ δ comes from:
--   - One δ from `𝕣-lim-self` (f δ to the limit)
--   - One δ from the symmetric direction
--
-- DIFFICULTY: High. Requires coinductive reasoning about stream approximations.
--
-- Proof strategy:
-- 1. Define L = lim (stream→ℝ ∘ f) coh (the Cauchy limit of the family)
-- 2. Prove limA-eq : stream→ℝ (limA f coh) ≡ L using eqℝ
-- 3. By 𝕣-lim-self: stream→ℝ (f δ) ∼[δ + δ] L
-- 4. Substitute L with stream→ℝ (limA f coh) using limA-eq
-- 5. Apply sym∼ to get the desired direction

-- Helper: the Cauchy limit of the stream family
limA-target : (f : ℚ₊ → 𝟛ᴺ) → (coh : ∀ δ ε → stream→ℝ (f δ) ∼[ δ +₊ ε ] stream→ℝ (f ε)) → ℝ
limA-target f coh = lim (stream→ℝ ∘ f) coh

-- Core lemma: stream→ℝ (limA f coh) equals the Cauchy limit
-- This requires showing ε-closeness for all ε
--
-- For any ε, we show stream→ℝ (limA f coh) ∼[ε] lim (stream→ℝ ∘ f) coh:
--   1. stream→ℝ (limA f coh) ∼[ε/2] rat (approxℚ₊ (limA f coh) (ε/4))  [by 𝕣-lim-self, sym∼]
--   2. Need: rat (approxℚ₊ (limA f coh) (ε/4)) close to stream→ℝ (f (ε/4))
--   3. stream→ℝ (f (ε/4)) ∼[ε/2] lim (stream→ℝ ∘ f) coh  [by 𝕣-lim-self]
--
-- Step 2 is the key technical challenge - it requires analyzing how limA constructs
-- its digits from the input streams.
--
-- PROOF STRATEGY for approx-limA-close:
-- =====================================
--
-- Goal: rat (approxℚ₊ (limA f coh) ε) ∼[ 2ε ] stream→ℝ (f ε)
--
-- Decomposition:
--   1. approxℚ₊ (limA f coh) ε = Σᵢ₌₀^(n-1) dᵢ/2^(i+1)  where n = ℚ₊→ℕ ε
--   2. Each digit dᵢ of limA comes from recursive construction:
--      - d₀: from f(1/16) sampled at precision 10
--      - d₁: from nextStreams(1/16), which involves f(1/256)
--      - dᵢ: from sampling at precision ≈ (1/16)^(i+1)
--
-- Key observations:
--   A. By coherence: stream→ℝ (f((1/16)^k)) ∼[(1/16)^k + ε] stream→ℝ (f ε)
--      So all samples are close to f ε.
--
--   B. The digit selection at each level "commits" to a value based on the
--      approximation threshold (±1/4). If approx(f(δ), prec) ≈ stream→ℝ (f ε),
--      then the chosen digit is consistent with stream→ℝ (f ε).
--
--   C. The tail bound: |stream→ℝ s - approx s n| < 1/2^n ≈ ε
--      (by modulus property)
--
-- Error accumulation:
--   - Each digit position i contributes error ≈ 2·(1/16)^(i+1) / 2^(i+1) from coherence
--   - Geometric sum: Σᵢ 2·(1/16)^(i+1) / 2^(i+1) < ε
--   - Tail truncation: < ε
--   - Total: < 2ε ✓
--
-- DIFFICULTY: High - requires coinductive analysis of limA structure
-- DEPENDENCY: This is the key lemma. Once proven, limA-eq and limA-close-to-input follow.
--
-- NOTE: Cannot use limA-eq here (circular dependency).
-- Must prove directly from digit construction.

module Approximation
  (approx-limA-close :
    (f : ℚ₊ → 𝟛ᴺ) →
    (coh : ∀ δ ε → stream→ℝ (f δ) ∼[ δ +₊ ε ] stream→ℝ (f ε)) →
    ∀ ε → rat (approxℚ₊ (limA f coh) ε) ∼[ ε +₊ ε ] stream→ℝ (f ε))
  where

  -- Prove the equality: stream→ℝ (limA f coh) ≡ lim (stream→ℝ ∘ f) coh
  limA-eq : (f : ℚ₊ → 𝟛ᴺ) →
            (coh : ∀ δ ε → stream→ℝ (f δ) ∼[ δ +₊ ε ] stream→ℝ (f ε)) →
            stream→ℝ (limA f coh) ≡ limA-target f coh
  limA-eq f coh = eqℝ (stream→ℝ (limA f coh)) (limA-target f coh) close-at-all-ε
    where
      L = limA-target f coh
      s = limA f coh

      -- Helper for ε/8 + ε/8 = ε/4
      /8₊+/8₊≡/4₊-ε : ∀ ε → /8₊ ε +₊ /8₊ ε ≡ /4₊ ε
      /8₊+/8₊≡/4₊-ε = /8₊+/8₊≡/4₊

      close-at-all-ε : ∀ ε → stream→ℝ s ∼[ ε ] L
      close-at-all-ε ε =
        let
          ε/4 = /4₊ ε
          ε/8 = /8₊ ε

          -- Step 1: rat (approxℚ₊ s (ε/8)) ∼[ε/8 + ε/8] stream→ℝ s = ∼[ε/4] stream→ℝ s
          -- By 𝕣-lim-self on the approximation sequence of s
          approx-to-stream-raw : rat (approxℚ₊ s ε/8) ∼[ ε/8 +₊ ε/8 ] stream→ℝ s
          approx-to-stream-raw = 𝕣-lim-self (λ ε' → rat (approxℚ₊ s ε')) (approxℚ₊-cauchy s) ε/8 ε/8

          -- Transport to ε/4
          approx-to-stream : rat (approxℚ₊ s ε/8) ∼[ ε/4 ] stream→ℝ s
          approx-to-stream = subst (λ x → rat (approxℚ₊ s ε/8) ∼[ x ] stream→ℝ s) (/8₊+/8₊≡/4₊-ε ε) approx-to-stream-raw

          -- Symmetric: stream→ℝ s ∼[ε/4] rat (approxℚ₊ s (ε/8))
          stream-to-approx : stream→ℝ s ∼[ ε/4 ] rat (approxℚ₊ s ε/8)
          stream-to-approx = sym∼ (rat (approxℚ₊ s ε/8)) (stream→ℝ s) ε/4 approx-to-stream

          -- Step 2: rat (approxℚ₊ s (ε/8)) ∼[ε/8 + ε/8] stream→ℝ (f (ε/8)) = ∼[ε/4]
          -- By the technical lemma approx-limA-close
          approx-to-f-raw : rat (approxℚ₊ s ε/8) ∼[ ε/8 +₊ ε/8 ] stream→ℝ (f ε/8)
          approx-to-f-raw = approx-limA-close f coh ε/8

          approx-to-f : rat (approxℚ₊ s ε/8) ∼[ ε/4 ] stream→ℝ (f ε/8)
          approx-to-f = subst (λ x → rat (approxℚ₊ s ε/8) ∼[ x ] stream→ℝ (f ε/8)) (/8₊+/8₊≡/4₊-ε ε) approx-to-f-raw

          -- Step 3: stream→ℝ (f (ε/8)) ∼[ε/8 + ε/8] L = ∼[ε/4]
          -- By 𝕣-lim-self on the family
          f-to-L-raw : stream→ℝ (f ε/8) ∼[ ε/8 +₊ ε/8 ] L
          f-to-L-raw = 𝕣-lim-self (stream→ℝ ∘ f) coh ε/8 ε/8

          f-to-L : stream→ℝ (f ε/8) ∼[ ε/4 ] L
          f-to-L = subst (λ x → stream→ℝ (f ε/8) ∼[ x ] L) (/8₊+/8₊≡/4₊-ε ε) f-to-L-raw

          -- Combine via triangle inequality:
          -- stream→ℝ s ∼[ε/4] rat (approxℚ₊ s ε/8) ∼[ε/4] stream→ℝ (f ε/8) ∼[ε/4] L
          -- Total: ε/4 + ε/4 + ε/4 = 3ε/4 < ε ✓
          -- But we need exactly ε, not 3ε/4. Use ε/4 + ε/2 = 3ε/4 bound for now,
          -- then weaken to ε.

          -- First combine stream-to-approx and approx-to-f: stream→ℝ s ∼[ε/4 + ε/4] stream→ℝ (f ε/8)
          step12-raw : stream→ℝ s ∼[ ε/4 +₊ ε/4 ] stream→ℝ (f ε/8)
          step12-raw = triangle∼ stream-to-approx approx-to-f

          step12 : stream→ℝ s ∼[ /2₊ ε ] stream→ℝ (f ε/8)
          step12 = subst (λ x → stream→ℝ s ∼[ x ] stream→ℝ (f ε/8)) (/4₊+/4₊≡/2₊ ε) step12-raw

          -- Now combine step12 and f-to-L: stream→ℝ s ∼[ε/2 + ε/4] L
          step123-raw : stream→ℝ s ∼[ /2₊ ε +₊ ε/4 ] L
          step123-raw = triangle∼ step12 f-to-L

          -- ε/2 + ε/4 = 3ε/4 < ε, so we can weaken the bound
          -- Using ∼→∼' : x ∼[ε] y → ε ≤ ε' → x ∼[ε'] y (closeness weakening)
          3/4-bound : /2₊ ε +₊ ε/4 ≡ /4₊ ε +₊ /2₊ ε
          3/4-bound = ℚ₊≡ ℚ!!

          -- Closeness can be weakened: if x ∼[ε] y and ε ≤ ε' then x ∼[ε'] y
          -- We have stream→ℝ s ∼[ε/2 + ε/4] L and need stream→ℝ s ∼[ε] L
          -- ε/2 + ε/4 = 3ε/4 ≤ ε, so this works

          -- 3ε/4 < ε follows from: 3ε/4 = 3/4 · ε < 1 · ε = ε (since 3/4 < 1 and ε > 0)
          -- Proof: (ε/2 + ε/4) + ε/4 = ε, and ε/4 > 0, so ε/2 + ε/4 < ε.
          --
          -- Step 1: 0 < ε/4 (using snd of ℚ₊)
          pos-ε/4 : 0ℚ < fst ε/4
          pos-ε/4 = 0<→< (fst ε/4) (snd ε/4)

          -- Step 2: Use <-o+ to get (ε/2 + ε/4) + 0 < (ε/2 + ε/4) + ε/4
          -- <-o+ a b c proof gives: c + a < c + b when proof : a < b
          step-raw : fst (/2₊ ε +₊ ε/4) ℚ.+ 0ℚ < fst (/2₊ ε +₊ ε/4) ℚ.+ fst ε/4
          step-raw = <-o+ 0ℚ (fst ε/4) (fst (/2₊ ε +₊ ε/4)) pos-ε/4

          -- Step 3: Simplify LHS: x + 0 = x
          step-lhs : fst (/2₊ ε +₊ ε/4) < fst (/2₊ ε +₊ ε/4) ℚ.+ fst ε/4
          step-lhs = subst (_< (fst (/2₊ ε +₊ ε/4) ℚ.+ fst ε/4)) (ℚP.+IdR (fst (/2₊ ε +₊ ε/4))) step-raw

          -- Step 4: Show RHS = (ε/2 + ε/4) + ε/4 = ε
          -- Using ℚ!! for the algebraic identity
          rhs-eq : fst (/2₊ ε +₊ ε/4) ℚ.+ fst ε/4 ≡ fst ε
          rhs-eq = ℚ!!

          three-quarter-lt-one : fst (/2₊ ε +₊ ε/4) < fst ε
          three-quarter-lt-one = subst (fst (/2₊ ε +₊ ε/4) <_) rhs-eq step-lhs

          bound-le : fst (/2₊ ε +₊ ε/4) ℚO.≤ fst ε
          bound-le = ℚO.<Weaken≤ _ _ three-quarter-lt-one

        in ∼-monotone≤ bound-le step123-raw

  -- Main theorem: limA produces streams close to input streams
  limA-close-to-input : (f : ℚ₊ → 𝟛ᴺ) →
                        (coh : ∀ δ ε → stream→ℝ (f δ) ∼[ δ +₊ ε ] stream→ℝ (f ε)) →
                        ∀ δ → stream→ℝ (limA f coh) ∼[ δ +₊ δ ] stream→ℝ (f δ)
  limA-close-to-input f coh δ =
    let
      L = limA-target f coh

      -- By 𝕣-lim-self: stream→ℝ (f δ) ∼[δ + δ] L
      f-to-L : stream→ℝ (f δ) ∼[ δ +₊ δ ] L
      f-to-L = 𝕣-lim-self (stream→ℝ ∘ f) coh δ δ

      -- Substitute L with stream→ℝ (limA f coh) using limA-eq
      f-to-limA : stream→ℝ (f δ) ∼[ δ +₊ δ ] stream→ℝ (limA f coh)
      f-to-limA = subst (λ x → stream→ℝ (f δ) ∼[ δ +₊ δ ] x) (sym (limA-eq f coh)) f-to-L

      -- Apply sym∼ to get the desired direction
    in sym∼ (stream→ℝ (f δ)) (stream→ℝ (limA f coh)) (δ +₊ δ) f-to-limA

-- Quotient lift (`limA-𝕀sd`, `limA-𝕀sd-close`) is intentionally deferred in
-- this phase. Direct-equivalence modules remain out-of-target until the core
-- approximation lemma is discharged constructively.
