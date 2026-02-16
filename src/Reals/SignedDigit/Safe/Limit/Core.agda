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
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sigma using (_×_; Σ; Σ-syntax)
open import Cubical.Data.Nat as ℕ renaming (_+_ to _+ℕ_; _·_ to _*ℕ_)
open import Cubical.Data.Nat.Properties as ℕP
open import Cubical.Data.Nat.Order as ℕO using (≤-k+; minGLB; ≤-refl) renaming (_≤_ to _≤ℕ_)
open import Cubical.Data.Nat.Mod as ℕMod using (log2ℕ)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Int
open import Cubical.Data.Rationals.Fast as ℚ
open import Cubical.Data.Rationals.Fast.Order as ℚO
open import Cubical.Data.Rationals.Fast.Properties as ℚP
open import Cubical.Data.Rationals.Fast.Order.Properties as ℚOP using (pos·abs; 0<sucN; /2₊; /4₊; ε/2+ε/2≡ε; /4₊+/4₊≡/2₊; /4₊≡/2₊/2₊; 0<pos; abs·abs; absComm-; decℚ<?; invℚ₊; ceilℚ₊)
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

open import Reals.SignedDigit.Safe.Limit.Core.RatLemmas public

-- Use the library's ℚ₊ addition (handles positivity proofs automatically)
_+₊_ : ℚ₊ → ℚ₊ → ℚ₊
_+₊_ = ℚO._ℚ₊+_

-- /16₊ ε = ε/16 (compose /4₊ twice)
/16₊ : ℚ₊ → ℚ₊
/16₊ ε = /4₊ (/4₊ ε)

-- Arithmetic lemmas for combining precision bounds
-- These follow from rational arithmetic and are proven using ℚ₊≡.

-- /2₊ (/2₊ ε) ≡ /4₊ ε (both are ε/4)
-- Proof: Use /4₊≡/2₊/2₊ from the library and lift via ℚ₊≡
/2₊∘/2₊≡/4₊ : ∀ ε → /2₊ (/2₊ ε) ≡ /4₊ ε
/2₊∘/2₊≡/4₊ ε = ℚ₊≡ (sym (/4₊≡/2₊/2₊ ε))

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

1/8ℚ : ℚ.ℚ
1/8ℚ = [ pos 1 / 1+ 7 ]

3/8ℚ : ℚ.ℚ
3/8ℚ = [ pos 3 / 1+ 7 ]

3/4ℚ : ℚ.ℚ
3/4ℚ = [ pos 3 / 1+ 3 ]

3/16ℚ : ℚ.ℚ
3/16ℚ = [ pos 3 / 1+ 15 ]

9/16ℚ : ℚ.ℚ
9/16ℚ = [ pos 9 / 1+ 15 ]

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

0<1/4 : ℚO.0< 1/4ℚ
0<1/4 = <→0< 1/4ℚ (ℚOP.0<pos 0 (1+ 3))

0<1/8 : ℚO.0< 1/8ℚ
0<1/8 = <→0< 1/8ℚ (ℚOP.0<pos 0 (1+ 7))

0<3/8 : ℚO.0< 3/8ℚ
0<3/8 = <→0< 3/8ℚ (ℚOP.0<pos 2 (1+ 7))

0<3/4 : ℚO.0< 3/4ℚ
0<3/4 = <→0< 3/4ℚ (ℚOP.0<pos 2 (1+ 3))

0<3/16 : ℚO.0< 3/16ℚ
0<3/16 = <→0< 3/16ℚ (ℚOP.0<pos 2 (1+ 15))

0<9/16 : ℚO.0< 9/16ℚ
0<9/16 = <→0< 9/16ℚ (ℚOP.0<pos 8 (1+ 15))

-- Bundle 1/16 as a positive rational
1/16ℚ₊ : ℚO.ℚ₊
1/16ℚ₊ = 1/16ℚ , 0<1/16

1/4ℚ₊ : ℚO.ℚ₊
1/4ℚ₊ = 1/4ℚ , 0<1/4

-- Normal form of ℚ₊→ℕ at 1/16 (used in finite-precision bounds)
ℚ₊→ℕ-1/16 : ℚ₊→ℕ 1/16ℚ₊ ≡ suc (suc (suc (suc (suc (suc zero)))))
ℚ₊→ℕ-1/16 = refl

min10-ℚ₊→ℕ-1/16 :
  ℕ.min 10n (ℚ₊→ℕ 1/16ℚ₊) ≡ suc (suc (suc (suc (suc (suc zero)))))
min10-ℚ₊→ℕ-1/16 = refl

1/8ℚ₊ : ℚO.ℚ₊
1/8ℚ₊ = 1/8ℚ , 0<1/8

3/8ℚ₊ : ℚO.ℚ₊
3/8ℚ₊ = 3/8ℚ , 0<3/8

3/4ℚ₊ : ℚO.ℚ₊
3/4ℚ₊ = 3/4ℚ , 0<3/4

3/16ℚ₊ : ℚO.ℚ₊
3/16ℚ₊ = 3/16ℚ , 0<3/16

9/16ℚ₊ : ℚO.ℚ₊
9/16ℚ₊ = 9/16ℚ , 0<9/16

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

x-y+y≡x-local : (x y : ℚ.ℚ) → (x ℚP.- y) ℚP.+ y ≡ x
x-y+y≡x-local x y =
  sym (ℚP.+Assoc x (ℚP.- y) y)
  ∙ cong (x ℚP.+_) (ℚP.+InvL y)
  ∙ ℚP.+IdR x

-- Multiplication monotonicity: c > 0 → a < b → c · a < c · b
-- Proof: Use <-·o from library with commutativity
<-·-mono-r : (c a b : ℚ.ℚ) → ℚO._<_ (ℚ.fromNat 0) c → a ℚO.< b → (c ℚP.· a) ℚO.< (c ℚP.· b)
<-·-mono-r c a b 0<c a<b = subst2 ℚO._<_ (ℚP.·Comm a c) (ℚP.·Comm b c) (<-·o a b c 0<c a<b)

plus-right-< : (a b c : ℚ.ℚ) → a ℚO.< b → (a ℚP.+ c) ℚO.< (b ℚP.+ c)
plus-right-< a b c a<b =
  subst2
    ℚO._<_
    (ℚP.+Comm c a)
    (ℚP.+Comm c b)
    (<-o+ a b c a<b)

plus-right-≤ : (a b c : ℚ.ℚ) → a ℚO.≤ b → (a ℚP.+ c) ℚO.≤ (b ℚP.+ c)
plus-right-≤ a b c a≤b =
  subst2
    ℚO._≤_
    (ℚP.+Comm c a)
    (ℚP.+Comm c b)
    (ℚO.≤-o+ a b c a≤b)

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

selectDigitQuarter : ℚ.ℚ → Digit
selectDigitQuarter q = case (q ℚO.≟ (ℚP.- 1/4ℚ)) of λ where
  (ℚO.lt _) → -1d
  (ℚO.eq _) → 0d
  (ℚO.gt _) → case (q ℚO.≟ 1/4ℚ) of λ where
    (ℚO.gt _) → +1d
    _         → 0d

baseApprox10 : (f : ℚ₊ → 𝟛ᴺ) → ℚ.ℚ
baseApprox10 f = approx (f 1/16ℚ₊) 10n

baseDigit : (f : ℚ₊ → 𝟛ᴺ) → Digit
baseDigit f = selectDigitQuarter (baseApprox10 f)

mul2-≤-local : {a b : ℚ.ℚ} → a ℚO.≤ b → (2Q ℚP.· a) ℚO.≤ (2Q ℚP.· b)
mul2-≤-local {a} {b} a≤b =
  subst2 ℚO._≤_ (ℚP.·Comm a 2Q) (ℚP.·Comm b 2Q)
    (ℚO.≤-·o a b 2Q 0≤2Q a≤b)

mul2-<-local : {a b : ℚ.ℚ} → a ℚO.< b → (2Q ℚP.· a) ℚO.< (2Q ℚP.· b)
mul2-<-local {a} {b} a<b =
  subst2 ℚO._<_ (ℚP.·Comm a 2Q) (ℚP.·Comm b 2Q)
    (ℚO.<-·o a b 2Q 0<2Q a<b)

expr--1d : (q : ℚ.ℚ) → (2Q ℚP.· q) ℚP.- digitToℚ -1d ≡ (2Q ℚP.· q) ℚP.+ 1Q
expr--1d q = ℚ!!

expr-0d-local : (q : ℚ.ℚ) → (2Q ℚP.· q) ℚP.- digitToℚ 0d ≡ 2Q ℚP.· q
expr-0d-local q = ℚ!!

expr-+1d-local : (q : ℚ.ℚ) → (2Q ℚP.· q) ℚP.- digitToℚ +1d ≡ (2Q ℚP.· q) ℚP.- 1Q
expr-+1d-local q = refl

-- bound→abs: If -ε < x < ε then |x| < ε
-- Proof: Use absFrom<×< from the library
bound→abs : (x ε : ℚ.ℚ) → (ℚP.- ε) ℚO.< x → x ℚO.< ε → ℚP.abs x ℚO.< ε
bound→abs x ε neg-bound pos-bound = absFrom<×< ε x neg-bound pos-bound

x<x+y : (x y : ℚ.ℚ) → 0ℚ ℚO.< y → x ℚO.< (x ℚP.+ y)
x<x+y x y 0<y =
  subst2 ℚO._<_ (ℚP.+IdR x) refl (<-o+ 0ℚ y x 0<y)

1/16<1/8 : 1/16ℚ ℚO.< 1/8ℚ
1/16<1/8 =
  subst (1/16ℚ ℚO.<_) rhs-eq (x<x+y 1/16ℚ 1/16ℚ (0<→< 1/16ℚ 0<1/16))
  where
    rhs-eq : 1/16ℚ ℚP.+ 1/16ℚ ≡ 1/8ℚ
    rhs-eq = ℚ!!

1/2<3/4 : inv2^ zero ℚO.< 3/4ℚ
1/2<3/4 =
  subst (inv2^ zero ℚO.<_) rhs-eq (x<x+y (inv2^ zero) 1/4ℚ (0<→< 1/4ℚ (<→0< 1/4ℚ (ℚOP.0<pos 0 (1+ 3)))))
  where
    rhs-eq : inv2^ zero ℚP.+ 1/4ℚ ≡ 3/4ℚ
    rhs-eq = ℚ!!

1/4<3/4 : 1/4ℚ ℚO.< 3/4ℚ
1/4<3/4 =
  subst (1/4ℚ ℚO.<_) rhs-eq (x<x+y 1/4ℚ (inv2^ zero) half-pos)
  where
    rhs-eq : 1/4ℚ ℚP.+ inv2^ zero ≡ 3/4ℚ
    rhs-eq = ℚ!!

    half-pos : 0ℚ ℚO.< inv2^ zero
    half-pos = 0<→< (inv2^ zero) (<→0< (inv2^ zero) (ℚOP.0<pos 0 (2^ℕ₊₁ (suc zero))))

1/2<1 : inv2^ zero ℚO.< 1Q
1/2<1 =
  subst (inv2^ zero ℚO.<_) rhs-eq (x<x+y (inv2^ zero) (inv2^ zero) half-pos)
  where
    half-pos : 0ℚ ℚO.< inv2^ zero
    half-pos = 0<→< (inv2^ zero) (<→0< (inv2^ zero) (ℚOP.0<pos 0 (2^ℕ₊₁ (suc zero))))

    rhs-eq : inv2^ zero ℚP.+ inv2^ zero ≡ 1Q
    rhs-eq = ℚ!!

1/2≤1 : inv2^ zero ℚO.≤ 1Q
1/2≤1 = <Weaken≤ (inv2^ zero) 1Q 1/2<1

1/4<1/2 : 1/4ℚ ℚO.< inv2^ zero
1/4<1/2 =
  subst (1/4ℚ ℚO.<_) rhs-eq (x<x+y 1/4ℚ 1/4ℚ (0<→< 1/4ℚ (<→0< 1/4ℚ (ℚOP.0<pos 0 (1+ 3)))))
  where
    rhs-eq : 1/4ℚ ℚP.+ 1/4ℚ ≡ inv2^ zero
    rhs-eq = ℚ!!

1/4≤1/2 : 1/4ℚ ℚO.≤ inv2^ zero
1/4≤1/2 = <Weaken≤ 1/4ℚ (inv2^ zero) 1/4<1/2

0≤1/4 : 0ℚ ℚO.≤ 1/4ℚ
0≤1/4 = <Weaken≤ 0ℚ 1/4ℚ (0<→< 1/4ℚ (<→0< 1/4ℚ (ℚOP.0<pos 0 (1+ 3))))

-1/4≤0 : (ℚP.- 1/4ℚ) ℚO.≤ 0ℚ
-1/4≤0 = ℚO.minus-≤ 0ℚ 1/4ℚ 0≤1/4

1/4≤1 : 1/4ℚ ℚO.≤ 1Q
1/4≤1 = ℚO.isTrans≤ 1/4ℚ (inv2^ zero) 1Q 1/4≤1/2 1/2≤1

-1/4<0 : (ℚP.- 1/4ℚ) ℚO.< 0ℚ
-1/4<0 =
  subst ((ℚP.- 1/4ℚ) ℚO.<_) rhs
    (x<x+y (ℚP.- 1/4ℚ) 1/4ℚ (0<→< 1/4ℚ 0<1/4))
  where
    rhs : (ℚP.- 1/4ℚ) ℚP.+ 1/4ℚ ≡ 0ℚ
    rhs = ℚ!!

-1/4<1/4 : (ℚP.- 1/4ℚ) ℚO.< 1/4ℚ
-1/4<1/4 = ℚO.isTrans< (ℚP.- 1/4ℚ) 0ℚ 1/4ℚ -1/4<0 (0<→< 1/4ℚ 0<1/4)

-1/2≤-1/4 : (ℚP.- inv2^ zero) ℚO.≤ (ℚP.- 1/4ℚ)
-1/2≤-1/4 = ℚO.minus-≤ 1/4ℚ (inv2^ zero) 1/4≤1/2

-1≤-1/2 : ℚP.- 1Q ℚO.≤ ℚP.- inv2^ zero
-1≤-1/2 = ℚO.minus-≤ (inv2^ zero) 1Q 1/2≤1

-1/2≤1 : ℚP.- inv2^ zero ℚO.≤ 1Q
-1/2≤1 =
  ℚO.isTrans≤ (ℚP.- inv2^ zero) 0ℚ 1Q neg-half≤0 0≤1
  where
    neg-half≤0 : ℚP.- inv2^ zero ℚO.≤ 0ℚ
    neg-half≤0 = ℚO.minus-≤ 0ℚ (inv2^ zero) (0≤inv2^ zero)

    0≤1 : 0ℚ ℚO.≤ 1Q
    0≤1 = <Weaken≤ 0ℚ 1Q (0<→< 1Q (<→0< 1Q (ℚOP.0<pos 0 (1+ 0))))

selectDigitQuarter<- :
  (q : ℚ.ℚ) →
  q ℚO.< (ℚP.- 1/4ℚ) →
  selectDigitQuarter q ≡ -1d
selectDigitQuarter<- q q<-1/4 with q ℚO.≟ (ℚP.- 1/4ℚ)
... | ℚO.lt _ = refl
... | ℚO.eq q=-1/4 =
  ⊥.rec
    (ℚO.isIrrefl<
      (ℚP.- 1/4ℚ)
      (subst
        (λ x → x ℚO.< (ℚP.- 1/4ℚ))
        q=-1/4
        q<-1/4))
... | ℚO.gt -1/4<q = ⊥.rec (ℚO.isIrrefl< q (ℚO.isTrans< q (ℚP.- 1/4ℚ) q q<-1/4 -1/4<q))

selectDigitQuarter> :
  (q : ℚ.ℚ) →
  1/4ℚ ℚO.< q →
  selectDigitQuarter q ≡ +1d
selectDigitQuarter> q 1/4<q with q ℚO.≟ (ℚP.- 1/4ℚ)
... | ℚO.lt q<-1/4 =
  ⊥.rec (ℚO.isIrrefl< q (ℚO.isTrans< q (ℚP.- 1/4ℚ) q q<-1/4 (ℚO.isTrans< (ℚP.- 1/4ℚ) 1/4ℚ q -1/4<1/4 1/4<q)))
... | ℚO.eq q=-1/4 =
  ⊥.rec
    (ℚO.isIrrefl<
      1/4ℚ
      (ℚO.isTrans<
        1/4ℚ
        (ℚP.- 1/4ℚ)
        1/4ℚ
        (subst (1/4ℚ ℚO.<_) q=-1/4 1/4<q)
        -1/4<1/4))
... | ℚO.gt -1/4<q with q ℚO.≟ 1/4ℚ
...   | ℚO.gt _ = refl
...   | ℚO.eq q=1/4 = ⊥.rec (ℚO.isIrrefl< 1/4ℚ (subst (1/4ℚ ℚO.<_) q=1/4 1/4<q))
...   | ℚO.lt q<1/4 = ⊥.rec (ℚO.isIrrefl< q (ℚO.isTrans< q 1/4ℚ q q<1/4 1/4<q))

selectDigitQuarter-between :
  (q : ℚ.ℚ) →
  (ℚP.- 1/4ℚ) ℚO.≤ q →
  q ℚO.≤ 1/4ℚ →
  selectDigitQuarter q ≡ 0d
selectDigitQuarter-between q -1/4≤q q≤1/4 with q ℚO.≟ (ℚP.- 1/4ℚ)
... | ℚO.lt q<-1/4 = ⊥.rec (ℚO.isIrrefl< (ℚP.- 1/4ℚ) (ℚO.isTrans≤< (ℚP.- 1/4ℚ) q (ℚP.- 1/4ℚ) -1/4≤q q<-1/4))
... | ℚO.eq _ = refl
... | ℚO.gt -1/4<q with q ℚO.≟ 1/4ℚ
...   | ℚO.gt 1/4<q = ⊥.rec (ℚO.isIrrefl< 1/4ℚ (ℚO.isTrans<≤ 1/4ℚ q 1/4ℚ 1/4<q q≤1/4))
...   | ℚO.eq _ = refl
...   | ℚO.lt _ = refl

digitContrib-0d-zero : digitContrib 0d zero ≡ 0ℚ
digitContrib-0d-zero = ·ZeroL (inv2^ zero)

limA-step :
  (f : ℚ₊ → 𝟛ᴺ) →
  (∀ δ ε → stream→ℝ (f δ) ∼[ δ +₊ ε ] stream→ℝ (f ε)) →
  Digit × (Σ[ nextStreams ∈ (ℚ₊ → 𝟛ᴺ) ]
    (∀ δ γ → stream→ℝ (nextStreams δ) ∼[ δ +₊ γ ] stream→ℝ (nextStreams γ)))
limA-step streams coh = d , (nextStreams , nextCoh)
  where
    -- Step 1: Fixed base sample at 1/16.
    s : 𝟛ᴺ
    s = streams 1/16ℚ₊
    
    q : ℚ.ℚ
    q = baseApprox10 streams

    d : Digit
    d = baseDigit streams

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
-- Helpers for limA-step projections and arithmetic unfolding
------------------------------------------------------------------------

stepDigit :
  (f : ℚ₊ → 𝟛ᴺ) →
  (coh : ∀ δ ε → stream→ℝ (f δ) ∼[ δ +₊ ε ] stream→ℝ (f ε)) →
  Digit
stepDigit f coh = baseDigit f

stepNextStreams :
  (f : ℚ₊ → 𝟛ᴺ) →
  (coh : ∀ δ ε → stream→ℝ (f δ) ∼[ δ +₊ ε ] stream→ℝ (f ε)) →
  ℚ₊ → 𝟛ᴺ
stepNextStreams f coh = fst (snd (limA-step f coh))

stepNextCoh :
  (f : ℚ₊ → 𝟛ᴺ) →
  (coh : ∀ δ ε → stream→ℝ (f δ) ∼[ δ +₊ ε ] stream→ℝ (f ε)) →
  ∀ δ γ → stream→ℝ (stepNextStreams f coh δ) ∼[ δ +₊ γ ] stream→ℝ (stepNextStreams f coh γ)
stepNextCoh f coh = snd (snd (limA-step f coh))

stepGetApprox :
  (f : ℚ₊ → 𝟛ᴺ) →
  (coh : ∀ δ ε → stream→ℝ (f δ) ∼[ δ +₊ ε ] stream→ℝ (f ε)) →
  ℚ₊ → ℚ.ℚ
stepGetApprox f coh δ = approx (f (/16₊ δ)) (ℚ₊→ℕ (/16₊ δ))

stepNextRat :
  (f : ℚ₊ → 𝟛ᴺ) →
  (coh : ∀ δ ε → stream→ℝ (f δ) ∼[ δ +₊ ε ] stream→ℝ (f ε)) →
  ℚ₊ → ℚ.ℚ
stepNextRat f coh δ = (2Q ℚP.· stepGetApprox f coh δ) ℚP.- digitToℚ (stepDigit f coh)

limA-tail-unfold :
  (f : ℚ₊ → 𝟛ᴺ) →
  (coh : ∀ δ ε → stream→ℝ (f δ) ∼[ δ +₊ ε ] stream→ℝ (f ε)) →
  tail (limA f coh) ≡ limA (stepNextStreams f coh) (stepNextCoh f coh)
limA-tail-unfold f coh = refl

stepNextStreams-def :
  (f : ℚ₊ → 𝟛ᴺ) →
  (coh : ∀ δ ε → stream→ℝ (f δ) ∼[ δ +₊ ε ] stream→ℝ (f ε)) →
  ∀ δ → stepNextStreams f coh δ ≡ rational→stream (clampℚ (stepNextRat f coh δ))
stepNextStreams-def f coh δ = refl

0<inv2^ : ∀ n → 0< (inv2^ n)
0<inv2^ n = <→0< (inv2^ n) (0<pos 0 (2^ℕ₊₁ (suc n)))

inv2^₊ : ℕ → ℚ₊
inv2^₊ n = inv2^ n , 0<inv2^ n

twoInv2₊ : ℕ → ℚ₊
twoInv2₊ n = inv2^₊ n +₊ inv2^₊ n

two-half : (x : ℚ.ℚ) → (2Q ℚP.· x) ℚP.· inv2^ zero ≡ x
two-half x =
  (2Q ℚP.· x) ℚP.· inv2^ zero
    ≡⟨ sym rhs-simp ⟩
  ((2Q ℚP.· x) ℚP.- 0ℚ) ℚP.· inv2^ zero
    ≡⟨ sym (base-half-step x 0ℚ) ⟩
  x ℚP.- (0ℚ ℚP.· inv2^ zero)
    ≡⟨ lhs-simp ⟩
  x
    ∎
  where
    lhs-simp : x ℚP.- (0ℚ ℚP.· inv2^ zero) ≡ x
    lhs-simp =
      cong (λ y → x ℚP.- y) (·ZeroL (inv2^ zero))
      ∙ minus-zero x

    rhs-simp : ((2Q ℚP.· x) ℚP.- 0ℚ) ℚP.· inv2^ zero ≡ (2Q ℚP.· x) ℚP.· inv2^ zero
    rhs-simp = cong (λ t → t ℚP.· inv2^ zero) (minus-zero (2Q ℚP.· x))

half-inv2^ : (k : ℕ) → inv2^ zero ℚP.· inv2^ k ≡ inv2^ (suc k)
half-inv2^ k =
  inv2^ zero ℚP.· inv2^ k
    ≡⟨ ℚP.·Comm (inv2^ zero) (inv2^ k) ⟩
  inv2^ k ℚP.· inv2^ zero
    ≡⟨ cong (λ t → t ℚP.· inv2^ zero) (sym (2·inv2^-suc k)) ⟩
  (2Q ℚP.· inv2^ (suc k)) ℚP.· inv2^ zero
    ≡⟨ two-half (inv2^ (suc k)) ⟩
  inv2^ (suc k)
    ∎

half-digitContrib : (d : Digit) (k : ℕ) →
  inv2^ zero ℚP.· digitContrib d k ≡ digitContrib d (suc k)
half-digitContrib d k =
  inv2^ zero ℚP.· digitContrib d k
    ≡⟨ refl ⟩
  inv2^ zero ℚP.· (digitToℚ d ℚP.· inv2^ k)
    ≡⟨ ℚP.·Assoc (inv2^ zero) (digitToℚ d) (inv2^ k) ⟩
  (inv2^ zero ℚP.· digitToℚ d) ℚP.· inv2^ k
    ≡⟨ cong (λ t → t ℚP.· inv2^ k) (ℚP.·Comm (inv2^ zero) (digitToℚ d)) ⟩
  (digitToℚ d ℚP.· inv2^ zero) ℚP.· inv2^ k
    ≡⟨ sym (ℚP.·Assoc (digitToℚ d) (inv2^ zero) (inv2^ k)) ⟩
  digitToℚ d ℚP.· (inv2^ zero ℚP.· inv2^ k)
    ≡⟨ cong (digitToℚ d ℚP.·_) (half-inv2^ k) ⟩
  digitToℚ d ℚP.· inv2^ (suc k)
    ≡⟨ refl ⟩
  digitContrib d (suc k)
    ∎

approx-unfold : (s : 𝟛ᴺ) (n : ℕ) →
  approx s (suc n)
  ≡ digitContrib (head s) zero ℚP.+ (inv2^ zero ℚP.· approx (tail s) n)
approx-unfold s zero =
  approx s (suc zero)
    ≡⟨ refl ⟩
  approx s zero ℚP.+ digitContrib (s ! suc zero) (suc zero)
    ≡⟨ refl ⟩
  digitContrib (head s) zero ℚP.+ digitContrib (tail s ! zero) (suc zero)
    ≡⟨ cong (digitContrib (head s) zero ℚP.+_) (sym (half-digitContrib (tail s ! zero) zero)) ⟩
  digitContrib (head s) zero ℚP.+ (inv2^ zero ℚP.· digitContrib (tail s ! zero) zero)
    ≡⟨ refl ⟩
  digitContrib (head s) zero ℚP.+ (inv2^ zero ℚP.· approx (tail s) zero)
    ∎
approx-unfold s (suc n) =
  approx s (suc (suc n))
    ≡⟨ refl ⟩
  approx s (suc n) ℚP.+ digitContrib (s ! suc (suc n)) (suc (suc n))
    ≡⟨ cong (λ t → t ℚP.+ digitContrib (s ! suc (suc n)) (suc (suc n))) (approx-unfold s n) ⟩
  (digitContrib (head s) zero ℚP.+ (inv2^ zero ℚP.· approx (tail s) n))
    ℚP.+ digitContrib (s ! suc (suc n)) (suc (suc n))
    ≡⟨ sym (ℚP.+Assoc (digitContrib (head s) zero) (inv2^ zero ℚP.· approx (tail s) n) (digitContrib (s ! suc (suc n)) (suc (suc n)))) ⟩
  digitContrib (head s) zero
    ℚP.+ ((inv2^ zero ℚP.· approx (tail s) n)
      ℚP.+ digitContrib (s ! suc (suc n)) (suc (suc n)))
    ≡⟨ cong (digitContrib (head s) zero ℚP.+_) step-tail ⟩
  digitContrib (head s) zero ℚP.+ (inv2^ zero ℚP.· approx (tail s) (suc n))
    ∎
  where
    step-tail :
      (inv2^ zero ℚP.· approx (tail s) n) ℚP.+ digitContrib (s ! suc (suc n)) (suc (suc n))
      ≡ inv2^ zero ℚP.· approx (tail s) (suc n)
    step-tail =
      (inv2^ zero ℚP.· approx (tail s) n) ℚP.+ digitContrib (s ! suc (suc n)) (suc (suc n))
        ≡⟨ cong ((inv2^ zero ℚP.· approx (tail s) n) ℚP.+_) (sym (half-digitContrib (tail s ! suc n) (suc n))) ⟩
      (inv2^ zero ℚP.· approx (tail s) n) ℚP.+ (inv2^ zero ℚP.· digitContrib (tail s ! suc n) (suc n))
        ≡⟨ sym (ℚP.·DistL+ (inv2^ zero) (approx (tail s) n) (digitContrib (tail s ! suc n) (suc n))) ⟩
      inv2^ zero ℚP.· (approx (tail s) n ℚP.+ digitContrib (tail s ! suc n) (suc n))
        ≡⟨ refl ⟩
      inv2^ zero ℚP.· approx (tail s) (suc n)
        ∎

next-roundtrip :
  (f : ℚ₊ → 𝟛ᴺ) →
  (coh : ∀ δ ε → stream→ℝ (f δ) ∼[ δ +₊ ε ] stream→ℝ (f ε)) →
  (δ : ℚ₊) →
  stream→ℝ (stepNextStreams f coh δ) ≡ rat (clampℚ (stepNextRat f coh δ))
next-roundtrip f coh δ =
  stream→ℝ (stepNextStreams f coh δ)
    ≡⟨ cong stream→ℝ (stepNextStreams-def f coh δ) ⟩
  stream→ℝ (rational→stream (clampℚ (stepNextRat f coh δ)))
    ≡⟨ round-trip-bounded (clampℚ (stepNextRat f coh δ)) lo hi ⟩
  rat (clampℚ (stepNextRat f coh δ))
    ∎
  where
    lo : (ℚP.- 1Q) ℚO.≤ clampℚ (stepNextRat f coh δ)
    lo = fst (abs≤1→interval (clampℚ (stepNextRat f coh δ)) (clampℚ-bound (stepNextRat f coh δ)))

    hi : clampℚ (stepNextRat f coh δ) ℚO.≤ 1Q
    hi = snd (abs≤1→interval (clampℚ (stepNextRat f coh δ)) (clampℚ-bound (stepNextRat f coh δ)))

getApprox-close :
  (f : ℚ₊ → 𝟛ᴺ) →
  (coh : ∀ δ ε → stream→ℝ (f δ) ∼[ δ +₊ ε ] stream→ℝ (f ε)) →
  (ε' ε : ℚ₊) →
  rat (stepGetApprox f coh ε')
    ∼[ /8₊ ε' +₊ (/16₊ ε' +₊ ε) ] stream→ℝ (f ε)
getApprox-close f coh ε' ε =
  triangle∼ step1 step2
  where
    sε' : 𝟛ᴺ
    sε' = f (/16₊ ε')

    step1-raw : rat (approxℚ₊ sε' (/16₊ ε')) ∼[ /16₊ ε' +₊ /16₊ ε' ] stream→ℝ sε'
    step1-raw = 𝕣-lim-self (λ η → rat (approxℚ₊ sε' η)) (approxℚ₊-cauchy sε') (/16₊ ε') (/16₊ ε')

    step1 : rat (stepGetApprox f coh ε') ∼[ /8₊ ε' ] stream→ℝ sε'
    step1 = subst (λ x → rat (stepGetApprox f coh ε') ∼[ x ] stream→ℝ sε') (/16₊+/16₊≡/8₊ ε') step1-raw

    step2 : stream→ℝ sε' ∼[ /16₊ ε' +₊ ε ] stream→ℝ (f ε)
    step2 = coh (/16₊ ε') ε

one≤ten : suc zero ≤ℕ 10n
one≤ten = 9 , refl

one≤suc : (n : ℕ) → suc zero ≤ℕ suc n
one≤suc n = n , ℕP.+-comm n (suc zero)

one≤min10-suc : (n : ℕ) → suc zero ≤ℕ ℕ.min 10n (suc n)
one≤min10-suc n = minGLB {x = suc zero} one≤ten (one≤suc n)

inv2^-mono-≤ : {m n : ℕ} → m ≤ℕ n → inv2^ n ℚO.≤ inv2^ m
inv2^-mono-≤ {m} {n} m≤n with ≤-k+ m≤n
... | k , p = subst (λ x → inv2^ x ℚO.≤ inv2^ m) (ℕP.+-comm m k ∙ p) (go k)
  where
    go : (k : ℕ) → inv2^ (m +ℕ k) ℚO.≤ inv2^ m
    go zero = subst (λ x → inv2^ x ℚO.≤ inv2^ m) (sym (ℕP.+-zero m)) (ℚO.isRefl≤ (inv2^ m))
    go (suc k) =
      let
        step1 : inv2^ (m +ℕ suc k) ℚO.≤ inv2^ (m +ℕ k)
        step1 = subst (λ x → inv2^ x ℚO.≤ inv2^ (m +ℕ k)) (sym (ℕP.+-suc m k)) (inv2^-mono (m +ℕ k))
      in ℚO.isTrans≤ _ _ _ step1 (go k)

inv2^min10-suc≤inv2^1 : (n : ℕ) → inv2^ (ℕ.min 10n (suc n)) ℚO.≤ inv2^ (suc zero)
inv2^min10-suc≤inv2^1 n = inv2^-mono-≤ (one≤min10-suc n)

ℚ₊→ℕ-suc : (ε : ℚ₊) → Σ[ n ∈ ℕ ] (ℚ₊→ℕ ε ≡ suc n)
ℚ₊→ℕ-suc ε with log2ℕ (ℕ₊₁→ℕ (fst (ceilℚ₊ (invℚ₊ ε))))
... | n , _ = n , refl

approx10-abs≤1 : (s : 𝟛ᴺ) → ℚP.abs (approx s 10n) ℚO.≤ 1Q
approx10-abs≤1 s =
  subst (λ x → ℚP.abs x ℚO.≤ 1Q) (sym sum-eq)
    (ℚO.isTrans≤ _ _ _ abs-sum
      sum-bound-1)
  where
    tail-bnd-raw : ℚP.abs (approx s 10n ℚP.- approx s zero) ℚO.≤ inv2^ (ℕ.min 10n zero)
    tail-bnd-raw = tail-bound-sym s 10n zero

    tail-bnd : ℚP.abs (approx s 10n ℚP.- approx s zero) ℚO.≤ inv2^ zero
    tail-bnd = subst (ℚP.abs (approx s 10n ℚP.- approx s zero) ℚO.≤_) refl tail-bnd-raw

    approx0-bnd : ℚP.abs (approx s zero) ℚO.≤ inv2^ zero
    approx0-bnd = subst (ℚP.abs (approx s zero) ℚO.≤_) refl (digitContrib-bound (s ! zero) zero)

    abs-sum :
      ℚP.abs ((approx s 10n ℚP.- approx s zero) ℚP.+ approx s zero)
      ℚO.≤ (ℚP.abs (approx s 10n ℚP.- approx s zero) ℚP.+ ℚP.abs (approx s zero))
    abs-sum = abs-triangle (approx s 10n ℚP.- approx s zero) (approx s zero)

    sum-bound :
      (ℚP.abs (approx s 10n ℚP.- approx s zero) ℚP.+ ℚP.abs (approx s zero))
      ℚO.≤ (inv2^ zero ℚP.+ inv2^ zero)
    sum-bound = ℚO.≤Monotone+ _ _ _ _ tail-bnd approx0-bnd

    half+half≡1 : inv2^ zero ℚP.+ inv2^ zero ≡ 1Q
    half+half≡1 = ℚ!!

    sum-bound-1 :
      (ℚP.abs (approx s 10n ℚP.- approx s zero) ℚP.+ ℚP.abs (approx s zero))
      ℚO.≤ 1Q
    sum-bound-1 =
      subst
        ((ℚP.abs (approx s 10n ℚP.- approx s zero) ℚP.+ ℚP.abs (approx s zero)) ℚO.≤_)
        half+half≡1
        sum-bound

    sum-eq : approx s 10n ≡ ((approx s 10n ℚP.- approx s zero) ℚP.+ approx s zero)
    sum-eq = sym (x-y+y≡x-local (approx s 10n) (approx s zero))

q10-abs≤1 : (f : ℚ₊ → 𝟛ᴺ) → ℚP.abs (approx (f 1/16ℚ₊) 10n) ℚO.≤ 1Q
q10-abs≤1 f = approx10-abs≤1 (f 1/16ℚ₊)

half-scale-rat∼ :
  {p q : ℚ.ℚ} →
  (ε : ℚ₊) →
  rat p ∼[ ε ] rat q →
  rat (inv2^ zero ℚP.· p) ∼[ /2₊ ε ] rat (inv2^ zero ℚP.· q)
half-scale-rat∼ {p} {q} ε p∼q =
  rat-rat-fromAbs (inv2^ zero ℚP.· p) (inv2^ zero ℚP.· q) (/2₊ ε)
    (subst
      (ℚP.abs ((inv2^ zero ℚP.· p) ℚP.- (inv2^ zero ℚP.· q)) ℚO.<_)
      half-bound
      (subst
        (λ t → t ℚO.< inv2^ zero ℚP.· fst ε)
        (sym abs-scale-diff)
        scaled))
  where
    raw-bounds :
      ((ℚP.- fst ε) ℚO.< (p ℚP.- q)) × ((p ℚP.- q) ℚO.< fst ε)
    raw-bounds = ∼→∼' (rat p) (rat q) ε p∼q

    abs-pq<ε : ℚP.abs (p ℚP.- q) ℚO.< fst ε
    abs-pq<ε = bound→abs (p ℚP.- q) (fst ε) (fst raw-bounds) (snd raw-bounds)

    scaled :
      inv2^ zero ℚP.· ℚP.abs (p ℚP.- q) ℚO.< inv2^ zero ℚP.· fst ε
    scaled =
      <-·-mono-r (inv2^ zero) (ℚP.abs (p ℚP.- q)) (fst ε)
        (0<→< (inv2^ zero) (0<inv2^ zero))
        abs-pq<ε

    abs-scale-diff :
      ℚP.abs ((inv2^ zero ℚP.· p) ℚP.- (inv2^ zero ℚP.· q))
      ≡ inv2^ zero ℚP.· ℚP.abs (p ℚP.- q)
    abs-scale-diff =
      cong ℚP.abs (·DistL- (inv2^ zero) p q)
      ∙ pos·abs (inv2^ zero) (p ℚP.- q) (0≤inv2^ zero)

    half-bound : inv2^ zero ℚP.· fst ε ≡ fst (/2₊ ε)
    half-bound = ℚ!!

affine-half-rat∼ :
  (d : Digit) →
  {p q : ℚ.ℚ} →
  (ε : ℚ₊) →
  rat p ∼[ ε ] rat q →
  rat (digitContrib d zero ℚP.+ (inv2^ zero ℚP.· p))
    ∼[ /2₊ ε ]
  rat (digitContrib d zero ℚP.+ (inv2^ zero ℚP.· q))
affine-half-rat∼ d {p} {q} ε p∼q =
  rat-rat-fromAbs
    (digitContrib d zero ℚP.+ (inv2^ zero ℚP.· p))
    (digitContrib d zero ℚP.+ (inv2^ zero ℚP.· q))
    (/2₊ ε)
    (subst
      (λ t → t ℚO.< fst (/2₊ ε))
      (sym (cong ℚP.abs (plus-cancel-same (digitContrib d zero) (inv2^ zero ℚP.· p) (inv2^ zero ℚP.· q))))
      half-abs-bound)
  where
    half-closeness :
      rat (inv2^ zero ℚP.· p) ∼[ /2₊ ε ] rat (inv2^ zero ℚP.· q)
    half-closeness = half-scale-rat∼ ε p∼q

    half-bounds :
      ((ℚP.- fst (/2₊ ε)) ℚO.< ((inv2^ zero ℚP.· p) ℚP.- (inv2^ zero ℚP.· q)))
      × (((inv2^ zero ℚP.· p) ℚP.- (inv2^ zero ℚP.· q)) ℚO.< fst (/2₊ ε))
    half-bounds = ∼→∼' (rat (inv2^ zero ℚP.· p)) (rat (inv2^ zero ℚP.· q)) (/2₊ ε) half-closeness

    half-abs-bound :
      ℚP.abs ((inv2^ zero ℚP.· p) ℚP.- (inv2^ zero ℚP.· q)) ℚO.< fst (/2₊ ε)
    half-abs-bound =
      bound→abs
        ((inv2^ zero ℚP.· p) ℚP.- (inv2^ zero ℚP.· q))
        (fst (/2₊ ε))
        (fst half-bounds)
        (snd half-bounds)

q10 : (f : ℚ₊ → 𝟛ᴺ) → ℚ.ℚ
q10 f = baseApprox10 f

q10-interval : (f : ℚ₊ → 𝟛ᴺ) → ((ℚP.- 1Q) ℚO.≤ q10 f) × (q10 f ℚO.≤ 1Q)
q10-interval f = abs≤1→interval (q10 f) (q10-abs≤1 f)

digit-half-to-quarter :
  (q : ℚ.ℚ) →
  ((ℚP.- 1Q) ℚO.≤ q) →
  (q ℚO.≤ 1Q) →
  rat (digitContrib (selectDigitQuarter q) zero) ∼[ 3/4ℚ₊ ] rat q
digit-half-to-quarter q q≥-1 q≤1 with q ℚO.≟ (ℚP.- 1/4ℚ)
... | ℚO.lt q<-1/4 =
  subst
    (λ d → rat (digitContrib d zero) ∼[ 3/4ℚ₊ ] rat q)
    sel-eq
    (finish abs≤1/2)
  where
    sel-eq : selectDigitQuarter q ≡ -1d
    sel-eq = selectDigitQuarter<- q q<-1/4

    q≤0 : q ℚO.≤ 0ℚ
    q≤0 = ℚO.isTrans≤ q (ℚP.- 1/4ℚ) 0ℚ (<Weaken≤ q (ℚP.- 1/4ℚ) q<-1/4) -1/4≤0

    0≤-q : 0ℚ ℚO.≤ (ℚP.- q)
    0≤-q = subst (λ t → t ℚO.≤ (ℚP.- q)) (sym (ℚP.-Invol 0ℚ)) (ℚO.minus-≤ q 0ℚ q≤0)

    -q≤1 : (ℚP.- q) ℚO.≤ 1Q
    -q≤1 = subst ((ℚP.- q) ℚO.≤_) (sym (ℚP.-Invol 1Q)) (ℚO.minus-≤ (ℚP.- 1Q) q q≥-1)

    lo-step : ((ℚP.- inv2^ zero) ℚP.+ 0ℚ) ℚO.≤ ((ℚP.- inv2^ zero) ℚP.+ (ℚP.- q))
    lo-step = ℚO.≤-o+ 0ℚ (ℚP.- q) (ℚP.- inv2^ zero) 0≤-q

    hi-step : ((ℚP.- inv2^ zero) ℚP.+ (ℚP.- q)) ℚO.≤ ((ℚP.- inv2^ zero) ℚP.+ 1Q)
    hi-step = ℚO.≤-o+ (ℚP.- q) 1Q (ℚP.- inv2^ zero) -q≤1

    lo-bnd :
      (ℚP.- inv2^ zero)
      ℚO.≤ (digitContrib (selectDigitQuarter q) zero ℚP.- q)
    lo-bnd =
      subst2
        ℚO._≤_
        (ℚP.+IdR (ℚP.- inv2^ zero))
        rhs
        lo-step
      where
        rhs : ((ℚP.- inv2^ zero) ℚP.+ (ℚP.- q)) ≡ (digitContrib (selectDigitQuarter q) zero ℚP.- q)
        rhs = ℚ!! ∙ sym (cong (λ d → digitContrib d zero ℚP.- q) sel-eq)

    hi-bnd :
      (digitContrib (selectDigitQuarter q) zero ℚP.- q)
      ℚO.≤ inv2^ zero
    hi-bnd =
      subst2
        ℚO._≤_
        lhs
        (subst (λ t → t ≡ inv2^ zero) (ℚP.+Comm (ℚP.- inv2^ zero) 1Q) ℚ!!)
        hi-step
      where
        lhs : ((ℚP.- inv2^ zero) ℚP.+ (ℚP.- q)) ≡ (digitContrib (selectDigitQuarter q) zero ℚP.- q)
        lhs = ℚ!! ∙ sym (cong (λ d → digitContrib d zero ℚP.- q) sel-eq)

    abs≤1/2 :
      ℚP.abs (digitContrib (selectDigitQuarter q) zero ℚP.- q) ℚO.≤ inv2^ zero
    abs≤1/2 = ℚO.absFrom≤×≤ (inv2^ zero) (digitContrib (selectDigitQuarter q) zero ℚP.- q) lo-bnd hi-bnd

    finish :
      ℚP.abs (digitContrib (selectDigitQuarter q) zero ℚP.- q) ℚO.≤ inv2^ zero →
      rat (digitContrib (selectDigitQuarter q) zero) ∼[ 3/4ℚ₊ ] rat q
    finish h =
      rat-rat-fromAbs
        (digitContrib (selectDigitQuarter q) zero)
        q
        3/4ℚ₊
        (≤<→< h 1/2<3/4)
... | ℚO.eq q=-1/4 =
  subst
    (λ d → rat (digitContrib d zero) ∼[ 3/4ℚ₊ ] rat q)
    sel-eq
    (finish abs≤1/2)
  where
    loq : (ℚP.- 1/4ℚ) ℚO.≤ q
    loq = subst ((ℚP.- 1/4ℚ) ℚO.≤_) (sym q=-1/4) (ℚO.isRefl≤ (ℚP.- 1/4ℚ))

    q<1/4 : q ℚO.< 1/4ℚ
    q<1/4 = subst (λ t → t ℚO.< 1/4ℚ) (sym q=-1/4) -1/4<1/4

    hiq : q ℚO.≤ 1/4ℚ
    hiq = <Weaken≤ q 1/4ℚ q<1/4

    sel-eq : selectDigitQuarter q ≡ 0d
    sel-eq = selectDigitQuarter-between q loq hiq

    neg-lo : (ℚP.- 1/4ℚ) ℚO.≤ (ℚP.- q)
    neg-lo = ℚO.minus-≤ q 1/4ℚ hiq

    neg-hi : (ℚP.- q) ℚO.≤ 1/4ℚ
    neg-hi = subst ((ℚP.- q) ℚO.≤_) (ℚP.-Invol 1/4ℚ) (ℚO.minus-≤ (ℚP.- 1/4ℚ) q loq)

    abs≤1/4 : ℚP.abs (ℚP.- q) ℚO.≤ 1/4ℚ
    abs≤1/4 = ℚO.absFrom≤×≤ 1/4ℚ (ℚP.- q) neg-lo neg-hi

    abs≤1/2 :
      ℚP.abs (digitContrib (selectDigitQuarter q) zero ℚP.- q) ℚO.≤ inv2^ zero
    abs≤1/2 =
      subst
        (λ d → ℚP.abs (digitContrib d zero ℚP.- q) ℚO.≤ inv2^ zero)
        (sym sel-eq)
        abs≤1/2-0
      where
        abs≤1/2-0 : ℚP.abs (digitContrib 0d zero ℚP.- q) ℚO.≤ inv2^ zero
        abs≤1/2-0 =
          subst
            (λ t → ℚP.abs t ℚO.≤ inv2^ zero)
            (sym eq0)
            (ℚO.isTrans≤ (ℚP.abs (ℚP.- q)) 1/4ℚ (inv2^ zero) abs≤1/4 1/4≤1/2)
          where
            eq0 : digitContrib 0d zero ℚP.- q ≡ (ℚP.- q)
            eq0 = cong (λ t → t ℚP.- q) digitContrib-0d-zero ∙ ℚP.+IdL (ℚP.- q)

    finish :
      ℚP.abs (digitContrib (selectDigitQuarter q) zero ℚP.- q) ℚO.≤ inv2^ zero →
      rat (digitContrib (selectDigitQuarter q) zero) ∼[ 3/4ℚ₊ ] rat q
    finish h =
      rat-rat-fromAbs
        (digitContrib (selectDigitQuarter q) zero)
        q
        3/4ℚ₊
        (≤<→< h 1/2<3/4)
... | ℚO.gt -1/4<q with q ℚO.≟ 1/4ℚ
...   | ℚO.gt 1/4<q =
  subst
    (λ d → rat (digitContrib d zero) ∼[ 3/4ℚ₊ ] rat q)
    sel-eq
    (finish abs≤1/2)
  where
    sel-eq : selectDigitQuarter q ≡ +1d
    sel-eq = selectDigitQuarter> q 1/4<q

    q≥0 : 0ℚ ℚO.≤ q
    q≥0 = ℚO.isTrans≤ 0ℚ 1/4ℚ q 0≤1/4 (<Weaken≤ 1/4ℚ q 1/4<q)

    -1≤-q : (ℚP.- 1Q) ℚO.≤ (ℚP.- q)
    -1≤-q = ℚO.minus-≤ q 1Q q≤1

    -q≤0 : (ℚP.- q) ℚO.≤ 0ℚ
    -q≤0 = ℚO.minus-≤ 0ℚ q q≥0

    lo-step : (inv2^ zero ℚP.+ (ℚP.- 1Q)) ℚO.≤ (inv2^ zero ℚP.+ (ℚP.- q))
    lo-step = ℚO.≤-o+ (ℚP.- 1Q) (ℚP.- q) (inv2^ zero) -1≤-q

    hi-step : (inv2^ zero ℚP.+ (ℚP.- q)) ℚO.≤ (inv2^ zero ℚP.+ 0ℚ)
    hi-step = ℚO.≤-o+ (ℚP.- q) 0ℚ (inv2^ zero) -q≤0

    lo-bnd :
      (ℚP.- inv2^ zero)
      ℚO.≤ (digitContrib (selectDigitQuarter q) zero ℚP.- q)
    lo-bnd =
      subst2
        ℚO._≤_
        (ℚ!!)
        rhs
        lo-step
      where
        rhs : (inv2^ zero ℚP.+ (ℚP.- q)) ≡ (digitContrib (selectDigitQuarter q) zero ℚP.- q)
        rhs = ℚ!! ∙ sym (cong (λ d → digitContrib d zero ℚP.- q) sel-eq)

    hi-bnd :
      (digitContrib (selectDigitQuarter q) zero ℚP.- q)
      ℚO.≤ inv2^ zero
    hi-bnd =
      subst2
        ℚO._≤_
        lhs
        (ℚP.+IdR (inv2^ zero))
        hi-step
      where
        lhs : (inv2^ zero ℚP.+ (ℚP.- q)) ≡ (digitContrib (selectDigitQuarter q) zero ℚP.- q)
        lhs = ℚ!! ∙ sym (cong (λ d → digitContrib d zero ℚP.- q) sel-eq)

    abs≤1/2 :
      ℚP.abs (digitContrib (selectDigitQuarter q) zero ℚP.- q) ℚO.≤ inv2^ zero
    abs≤1/2 = ℚO.absFrom≤×≤ (inv2^ zero) (digitContrib (selectDigitQuarter q) zero ℚP.- q) lo-bnd hi-bnd

    finish :
      ℚP.abs (digitContrib (selectDigitQuarter q) zero ℚP.- q) ℚO.≤ inv2^ zero →
      rat (digitContrib (selectDigitQuarter q) zero) ∼[ 3/4ℚ₊ ] rat q
    finish h =
      rat-rat-fromAbs
        (digitContrib (selectDigitQuarter q) zero)
        q
        3/4ℚ₊
        (≤<→< h 1/2<3/4)
...   | ℚO.eq q=1/4 =
  subst
    (λ d → rat (digitContrib d zero) ∼[ 3/4ℚ₊ ] rat q)
    sel-eq
    (finish abs≤1/2)
  where
    loq : (ℚP.- 1/4ℚ) ℚO.≤ q
    loq = <Weaken≤ (ℚP.- 1/4ℚ) q -1/4<q

    hiq : q ℚO.≤ 1/4ℚ
    hiq = subst (λ t → t ℚO.≤ 1/4ℚ) (sym q=1/4) (ℚO.isRefl≤ 1/4ℚ)

    sel-eq : selectDigitQuarter q ≡ 0d
    sel-eq = selectDigitQuarter-between q loq hiq

    neg-lo : (ℚP.- 1/4ℚ) ℚO.≤ (ℚP.- q)
    neg-lo = ℚO.minus-≤ q 1/4ℚ hiq

    neg-hi : (ℚP.- q) ℚO.≤ 1/4ℚ
    neg-hi = subst ((ℚP.- q) ℚO.≤_) (ℚP.-Invol 1/4ℚ) (ℚO.minus-≤ (ℚP.- 1/4ℚ) q loq)

    abs≤1/4 : ℚP.abs (ℚP.- q) ℚO.≤ 1/4ℚ
    abs≤1/4 = ℚO.absFrom≤×≤ 1/4ℚ (ℚP.- q) neg-lo neg-hi

    abs≤1/2 :
      ℚP.abs (digitContrib (selectDigitQuarter q) zero ℚP.- q) ℚO.≤ inv2^ zero
    abs≤1/2 =
      subst
        (λ d → ℚP.abs (digitContrib d zero ℚP.- q) ℚO.≤ inv2^ zero)
        (sym sel-eq)
        abs≤1/2-0
      where
        abs≤1/2-0 : ℚP.abs (digitContrib 0d zero ℚP.- q) ℚO.≤ inv2^ zero
        abs≤1/2-0 =
          subst
            (λ t → ℚP.abs t ℚO.≤ inv2^ zero)
            (sym eq0)
            (ℚO.isTrans≤ (ℚP.abs (ℚP.- q)) 1/4ℚ (inv2^ zero) abs≤1/4 1/4≤1/2)
          where
            eq0 : digitContrib 0d zero ℚP.- q ≡ (ℚP.- q)
            eq0 = cong (λ t → t ℚP.- q) digitContrib-0d-zero ∙ ℚP.+IdL (ℚP.- q)

    finish :
      ℚP.abs (digitContrib (selectDigitQuarter q) zero ℚP.- q) ℚO.≤ inv2^ zero →
      rat (digitContrib (selectDigitQuarter q) zero) ∼[ 3/4ℚ₊ ] rat q
    finish h =
      rat-rat-fromAbs
        (digitContrib (selectDigitQuarter q) zero)
        q
        3/4ℚ₊
        (≤<→< h 1/2<3/4)
...   | ℚO.lt q<1/4 =
  subst
    (λ d → rat (digitContrib d zero) ∼[ 3/4ℚ₊ ] rat q)
    sel-eq
    (finish abs≤1/2)
  where
    loq : (ℚP.- 1/4ℚ) ℚO.≤ q
    loq = <Weaken≤ (ℚP.- 1/4ℚ) q -1/4<q

    hiq : q ℚO.≤ 1/4ℚ
    hiq = <Weaken≤ q 1/4ℚ q<1/4

    sel-eq : selectDigitQuarter q ≡ 0d
    sel-eq = selectDigitQuarter-between q loq hiq

    neg-lo : (ℚP.- 1/4ℚ) ℚO.≤ (ℚP.- q)
    neg-lo = ℚO.minus-≤ q 1/4ℚ hiq

    neg-hi : (ℚP.- q) ℚO.≤ 1/4ℚ
    neg-hi = subst ((ℚP.- q) ℚO.≤_) (ℚP.-Invol 1/4ℚ) (ℚO.minus-≤ (ℚP.- 1/4ℚ) q loq)

    abs≤1/4 : ℚP.abs (ℚP.- q) ℚO.≤ 1/4ℚ
    abs≤1/4 = ℚO.absFrom≤×≤ 1/4ℚ (ℚP.- q) neg-lo neg-hi

    abs≤1/2 :
      ℚP.abs (digitContrib (selectDigitQuarter q) zero ℚP.- q) ℚO.≤ inv2^ zero
    abs≤1/2 =
      subst
        (λ d → ℚP.abs (digitContrib d zero ℚP.- q) ℚO.≤ inv2^ zero)
        (sym sel-eq)
        abs≤1/2-0
      where
        abs≤1/2-0 : ℚP.abs (digitContrib 0d zero ℚP.- q) ℚO.≤ inv2^ zero
        abs≤1/2-0 =
          subst
            (λ t → ℚP.abs t ℚO.≤ inv2^ zero)
            (sym eq0)
            (ℚO.isTrans≤ (ℚP.abs (ℚP.- q)) 1/4ℚ (inv2^ zero) abs≤1/4 1/4≤1/2)
          where
            eq0 : digitContrib 0d zero ℚP.- q ≡ (ℚP.- q)
            eq0 = cong (λ t → t ℚP.- q) digitContrib-0d-zero ∙ ℚP.+IdL (ℚP.- q)

    finish :
      ℚP.abs (digitContrib (selectDigitQuarter q) zero ℚP.- q) ℚO.≤ inv2^ zero →
      rat (digitContrib (selectDigitQuarter q) zero) ∼[ 3/4ℚ₊ ] rat q
    finish h =
      rat-rat-fromAbs
        (digitContrib (selectDigitQuarter q) zero)
        q
        3/4ℚ₊
        (≤<→< h 1/2<3/4)

abstract
  digit-half-to-q10 :
    (f : ℚ₊ → 𝟛ᴺ) →
    rat (digitContrib (baseDigit f) zero) ∼[ 3/4ℚ₊ ] rat (q10 f)
  digit-half-to-q10 f = digit-half-to-quarter (q10 f) (fst (q10-interval f)) (snd (q10-interval f))

  q10-to-approx16 :
    (f : ℚ₊ → 𝟛ᴺ) →
    rat (q10 f) ∼[ 1/16ℚ₊ ] rat (approxℚ₊ (f 1/16ℚ₊) 1/16ℚ₊)
  q10-to-approx16 f =
    rat-rat-fromAbs
      (q10 f)
      (approxℚ₊ s 1/16ℚ₊)
      1/16ℚ₊
      abs<
    where
      s : 𝟛ᴺ
      s = f 1/16ℚ₊

      tail≤ :
        ℚP.abs (q10 f ℚP.- approxℚ₊ s 1/16ℚ₊)
        ℚO.≤ inv2^ (suc (suc (suc (suc (suc (suc zero))))))
      tail≤ =
        subst
          (ℚP.abs (q10 f ℚP.- approxℚ₊ s 1/16ℚ₊) ℚO.≤_)
          (cong inv2^ min10-ℚ₊→ℕ-1/16)
          (tail-bound-sym s 10n (ℚ₊→ℕ 1/16ℚ₊))

      mod16 :
        inv2^ (suc (suc (suc (suc (suc (suc zero))))))
        ℚO.< fst 1/16ℚ₊
      mod16 =
        subst
          (λ x → x ℚO.< fst 1/16ℚ₊)
          (cong inv2^ ℚ₊→ℕ-1/16)
          (modulus-correct 1/16ℚ₊)

      abs< : ℚP.abs (q10 f ℚP.- approxℚ₊ s 1/16ℚ₊) ℚO.< fst 1/16ℚ₊
      abs< = ≤<→< tail≤ mod16

  q10-to-baseStream :
    (f : ℚ₊ → 𝟛ᴺ) →
    rat (q10 f) ∼[ 3/16ℚ₊ ] stream→ℝ (f 1/16ℚ₊)
  q10-to-baseStream f =
    subst
      (λ x → rat (q10 f) ∼[ x ] stream→ℝ (f 1/16ℚ₊))
      (ℚ₊≡ ℚ!!)
      (triangle∼ q10≈approx16 approx16≈stream)
    where
      s : 𝟛ᴺ
      s = f 1/16ℚ₊

      q10≈approx16 : rat (q10 f) ∼[ 1/16ℚ₊ ] rat (approxℚ₊ s 1/16ℚ₊)
      q10≈approx16 = q10-to-approx16 f

      approx16≈stream-raw :
        rat (approxℚ₊ s 1/16ℚ₊) ∼[ 1/16ℚ₊ +₊ 1/16ℚ₊ ] stream→ℝ s
      approx16≈stream-raw =
        𝕣-lim-self
          (λ ε' → rat (approxℚ₊ s ε'))
          (approxℚ₊-cauchy s)
          1/16ℚ₊
          1/16ℚ₊

      approx16≈stream : rat (approxℚ₊ s 1/16ℚ₊) ∼[ 1/8ℚ₊ ] stream→ℝ s
      approx16≈stream =
        subst
          (λ x → rat (approxℚ₊ s 1/16ℚ₊) ∼[ x ] stream→ℝ s)
          (ℚ₊≡ ℚ!!)
          approx16≈stream-raw

  zero≤ℕ : (n : ℕ) → zero ≤ℕ n
  zero≤ℕ n = n , ℕP.+-zero n

  approx-abs≤1 : (s : 𝟛ᴺ) (n : ℕ) → ℚP.abs (approx s n) ℚO.≤ 1Q
  approx-abs≤1 s n =
    subst (λ x → ℚP.abs x ℚO.≤ 1Q) (sym sum-eq)
      (ℚO.isTrans≤ _ _ _ abs-sum sum-bound-1)
    where
      tail-bnd-raw : ℚP.abs (approx s n ℚP.- approx s zero) ℚO.≤ inv2^ (ℕ.min n zero)
      tail-bnd-raw = tail-bound-sym s n zero

      tail-bnd : ℚP.abs (approx s n ℚP.- approx s zero) ℚO.≤ inv2^ zero
      tail-bnd =
        subst
          (ℚP.abs (approx s n ℚP.- approx s zero) ℚO.≤_)
          (cong inv2^ (min-eq-right n zero (zero≤ℕ n)))
          tail-bnd-raw

      approx0-bnd : ℚP.abs (approx s zero) ℚO.≤ inv2^ zero
      approx0-bnd = subst (ℚP.abs (approx s zero) ℚO.≤_) refl (digitContrib-bound (s ! zero) zero)

      abs-sum :
        ℚP.abs ((approx s n ℚP.- approx s zero) ℚP.+ approx s zero)
        ℚO.≤ (ℚP.abs (approx s n ℚP.- approx s zero) ℚP.+ ℚP.abs (approx s zero))
      abs-sum = abs-triangle (approx s n ℚP.- approx s zero) (approx s zero)

      sum-bound :
        (ℚP.abs (approx s n ℚP.- approx s zero) ℚP.+ ℚP.abs (approx s zero))
        ℚO.≤ (inv2^ zero ℚP.+ inv2^ zero)
      sum-bound = ℚO.≤Monotone+ _ _ _ _ tail-bnd approx0-bnd

      half+half≡1 : inv2^ zero ℚP.+ inv2^ zero ≡ 1Q
      half+half≡1 = ℚ!!

      sum-bound-1 :
        (ℚP.abs (approx s n ℚP.- approx s zero) ℚP.+ ℚP.abs (approx s zero))
        ℚO.≤ 1Q
      sum-bound-1 =
        subst
          ((ℚP.abs (approx s n ℚP.- approx s zero) ℚP.+ ℚP.abs (approx s zero)) ℚO.≤_)
          half+half≡1
          sum-bound

      sum-eq : approx s n ≡ ((approx s n ℚP.- approx s zero) ℚP.+ approx s zero)
      sum-eq = sym (x-y+y≡x-local (approx s n) (approx s zero))

  stepGetApprox-abs≤1 :
    (f : ℚ₊ → 𝟛ᴺ) →
    (coh : ∀ δ ε → stream→ℝ (f δ) ∼[ δ +₊ ε ] stream→ℝ (f ε)) →
    (ε' : ℚ₊) →
    ℚP.abs (stepGetApprox f coh ε') ℚO.≤ 1Q
  stepGetApprox-abs≤1 f coh ε' = approx-abs≤1 (f (/16₊ ε')) (ℚ₊→ℕ (/16₊ ε'))

  stepGetApprox-interval :
    (f : ℚ₊ → 𝟛ᴺ) →
    (coh : ∀ δ ε → stream→ℝ (f δ) ∼[ δ +₊ ε ] stream→ℝ (f ε)) →
    (ε' : ℚ₊) →
    ((ℚP.- 1Q) ℚO.≤ stepGetApprox f coh ε') × (stepGetApprox f coh ε' ℚO.≤ 1Q)
  stepGetApprox-interval f coh ε' = abs≤1→interval (stepGetApprox f coh ε') (stepGetApprox-abs≤1 f coh ε')

  getApprox-to-q10 :
    (f : ℚ₊ → 𝟛ᴺ) →
    (coh : ∀ δ ε → stream→ℝ (f δ) ∼[ δ +₊ ε ] stream→ℝ (f ε)) →
    (ε' : ℚ₊) →
    rat (stepGetApprox f coh ε') ∼[ ((/8₊ ε' +₊ /16₊ ε') +₊ 1/4ℚ₊) ] rat (q10 f)
  getApprox-to-q10 f coh ε' =
    subst
      (λ x → rat (stepGetApprox f coh ε') ∼[ x ] rat (q10 f))
      (ℚ₊≡ ℚ!!)
      (triangle∼ toBase baseToQ10)
    where
      toBase :
        rat (stepGetApprox f coh ε')
        ∼[ /8₊ ε' +₊ (/16₊ ε' +₊ 1/16ℚ₊) ]
        stream→ℝ (f 1/16ℚ₊)
      toBase = getApprox-close f coh ε' 1/16ℚ₊

      baseToQ10 : stream→ℝ (f 1/16ℚ₊) ∼[ 3/16ℚ₊ ] rat (q10 f)
      baseToQ10 =
        sym∼
          (rat (q10 f))
          (stream→ℝ (f 1/16ℚ₊))
          3/16ℚ₊
          (q10-to-baseStream f)

  ζ : ℚ₊ → ℚ₊
  ζ ε' = /8₊ ε' +₊ /16₊ ε'

  twoζ : ℚ₊ → ℚ₊
  twoζ ε' = ζ ε' +₊ ζ ε'

  β : ℚ₊ → ℚ₊
  β ε' = ζ ε' +₊ 1/4ℚ₊

  getApprox-q10-bounds :
    (f : ℚ₊ → 𝟛ᴺ) →
    (coh : ∀ δ ε → stream→ℝ (f δ) ∼[ δ +₊ ε ] stream→ℝ (f ε)) →
    (ε' : ℚ₊) →
    ((ℚP.- fst (β ε')) ℚO.< (stepGetApprox f coh ε' ℚP.- q10 f))
    × ((stepGetApprox f coh ε' ℚP.- q10 f) ℚO.< fst (β ε'))
  getApprox-q10-bounds f coh ε' =
    ∼→∼'
      (rat (stepGetApprox f coh ε'))
      (rat (q10 f))
      (β ε')
      (subst
        (λ x → rat (stepGetApprox f coh ε') ∼[ x ] rat (q10 f))
        (ℚ₊≡ ℚ!!)
        (getApprox-to-q10 f coh ε'))

  getApprox-q10-abs< :
    (f : ℚ₊ → 𝟛ᴺ) →
    (coh : ∀ δ ε → stream→ℝ (f δ) ∼[ δ +₊ ε ] stream→ℝ (f ε)) →
    (ε' : ℚ₊) →
    ℚP.abs (stepGetApprox f coh ε' ℚP.- q10 f) ℚO.< fst (β ε')
  getApprox-q10-abs< f coh ε' =
    bound→abs
      (stepGetApprox f coh ε' ℚP.- q10 f)
      (fst (β ε'))
      (fst (getApprox-q10-bounds f coh ε'))
      (snd (getApprox-q10-bounds f coh ε'))

  getApprox<q10+β :
    (f : ℚ₊ → 𝟛ᴺ) →
    (coh : ∀ δ ε → stream→ℝ (f δ) ∼[ δ +₊ ε ] stream→ℝ (f ε)) →
    (ε' : ℚ₊) →
    stepGetApprox f coh ε' ℚO.< (q10 f ℚP.+ fst (β ε'))
  getApprox<q10+β f coh ε' =
    subst2
      ℚO._<_
      lhs-eq
      rhs-eq
      step
    where
      g : ℚ.ℚ
      g = stepGetApprox f coh ε'

      q : ℚ.ℚ
      q = q10 f

      bnd : (stepGetApprox f coh ε' ℚP.- q10 f) ℚO.< fst (β ε')
      bnd = snd (getApprox-q10-bounds f coh ε')

      step : (q ℚP.+ (g ℚP.- q)) ℚO.< (q ℚP.+ fst (β ε'))
      step = <-o+ (g ℚP.- q) (fst (β ε')) q bnd

      lhs-eq : q ℚP.+ (g ℚP.- q) ≡ g
      lhs-eq = ℚP.+Comm q (g ℚP.- q) ∙ x-y+y≡x-local g q

      rhs-eq : q ℚP.+ fst (β ε') ≡ q ℚP.+ fst (β ε')
      rhs-eq = refl

  q10<getApprox+β :
    (f : ℚ₊ → 𝟛ᴺ) →
    (coh : ∀ δ ε → stream→ℝ (f δ) ∼[ δ +₊ ε ] stream→ℝ (f ε)) →
    (ε' : ℚ₊) →
    q10 f ℚO.< (stepGetApprox f coh ε' ℚP.+ fst (β ε'))
  q10<getApprox+β f coh ε' =
    subst2
      ℚO._<_
      lhs-eq
      rhs-eq
      step2
    where
      g : ℚ.ℚ
      g = stepGetApprox f coh ε'

      q : ℚ.ℚ
      q = q10 f

      bnd : (ℚP.- fst (β ε')) ℚO.< (stepGetApprox f coh ε' ℚP.- q10 f)
      bnd = fst (getApprox-q10-bounds f coh ε')

      step1 : (q ℚP.+ (ℚP.- fst (β ε'))) ℚO.< (q ℚP.+ (g ℚP.- q))
      step1 = <-o+ (ℚP.- fst (β ε')) (g ℚP.- q) q bnd

      step2 :
        (fst (β ε') ℚP.+ (q ℚP.+ (ℚP.- fst (β ε'))))
        ℚO.<
        (fst (β ε') ℚP.+ (q ℚP.+ (g ℚP.- q)))
      step2 = <-o+ (q ℚP.+ (ℚP.- fst (β ε'))) (q ℚP.+ (g ℚP.- q)) (fst (β ε')) step1

      lhs-eq : fst (β ε') ℚP.+ (q ℚP.+ (ℚP.- fst (β ε'))) ≡ q
      lhs-eq =
        fst (β ε') ℚP.+ (q ℚP.+ (ℚP.- fst (β ε')))
          ≡⟨ cong (fst (β ε') ℚP.+_) (ℚP.+Comm q (ℚP.- fst (β ε'))) ⟩
        fst (β ε') ℚP.+ ((ℚP.- fst (β ε')) ℚP.+ q)
          ≡⟨ ℚP.+Assoc (fst (β ε')) (ℚP.- fst (β ε')) q ⟩
        (fst (β ε') ℚP.+ (ℚP.- fst (β ε'))) ℚP.+ q
          ≡⟨ cong (λ t → t ℚP.+ q) (ℚP.+InvR (fst (β ε'))) ⟩
        0ℚ ℚP.+ q
          ≡⟨ ℚP.+IdL q ⟩
        q
          ∎

      rhs-eq : fst (β ε') ℚP.+ (q ℚP.+ (g ℚP.- q)) ≡ (g ℚP.+ fst (β ε'))
      rhs-eq =
        fst (β ε') ℚP.+ (q ℚP.+ (g ℚP.- q))
          ≡⟨ cong (fst (β ε') ℚP.+_) (ℚP.+Comm q (g ℚP.- q) ∙ x-y+y≡x-local g q) ⟩
        fst (β ε') ℚP.+ g
          ≡⟨ ℚP.+Comm (fst (β ε')) g ⟩
        g ℚP.+ fst (β ε')
          ∎

  ε≤ε+ε : (ε : ℚ₊) → fst ε ℚO.≤ fst (ε +₊ ε)
  ε≤ε+ε ε = <Weaken≤ (fst ε) (fst (ε +₊ ε)) ε<ε+ε
    where
      ε<ε+ε : fst ε ℚO.< fst (ε +₊ ε)
      ε<ε+ε =
        subst (fst ε ℚO.<_) (ℚ!!) (x<x+y (fst ε) (fst ε) (0<→< (fst ε) (snd ε)))

  0<twoζ : (ε' : ℚ₊) → ℚO.0< (fst (twoζ ε'))
  0<twoζ ε' = snd (twoζ ε')

  -1-twoζ<-1 : (ε' : ℚ₊) → ((ℚP.- 1Q) ℚP.- fst (twoζ ε')) ℚO.< (ℚP.- 1Q)
  -1-twoζ<-1 ε' =
    subst
      (((ℚP.- 1Q) ℚP.- fst (twoζ ε')) ℚO.<_)
      rhs-eq
      step
    where
      step : ((ℚP.- 1Q) ℚP.- fst (twoζ ε')) ℚO.< (((ℚP.- 1Q) ℚP.- fst (twoζ ε')) ℚP.+ fst (twoζ ε'))
      step = x<x+y (((ℚP.- 1Q) ℚP.- fst (twoζ ε')) ) (fst (twoζ ε')) (0<→< (fst (twoζ ε')) (0<twoζ ε'))

      rhs-eq : ((((ℚP.- 1Q) ℚP.- fst (twoζ ε')) ℚP.+ fst (twoζ ε'))) ≡ (ℚP.- 1Q)
      rhs-eq = ℚ!!

  1<1+twoζ : (ε' : ℚ₊) → 1Q ℚO.< (1Q ℚP.+ fst (twoζ ε'))
  1<1+twoζ ε' = x<x+y 1Q (fst (twoζ ε')) (0<→< (fst (twoζ ε')) (0<twoζ ε'))

  -1<1 : (ℚP.- 1Q) ℚO.< 1Q
  -1<1 = subst ((ℚP.- 1Q) ℚO.<_) rhs (x<x+y (ℚP.- 1Q) 2Q 0<2Q)
    where
      rhs : (ℚP.- 1Q) ℚP.+ 2Q ≡ 1Q
      rhs = ℚ!!

  stepDigit-neg :
    (f : ℚ₊ → 𝟛ᴺ) →
    (coh : ∀ δ ε → stream→ℝ (f δ) ∼[ δ +₊ ε ] stream→ℝ (f ε)) →
    q10 f ℚO.< (ℚP.- 1/4ℚ) →
    stepDigit f coh ≡ -1d
  stepDigit-neg f coh q<-1/4 = selectDigitQuarter<- (q10 f) q<-1/4

  stepDigit-mid :
    (f : ℚ₊ → 𝟛ᴺ) →
    (coh : ∀ δ ε → stream→ℝ (f δ) ∼[ δ +₊ ε ] stream→ℝ (f ε)) →
    (ℚP.- 1/4ℚ) ℚO.≤ q10 f →
    q10 f ℚO.≤ 1/4ℚ →
    stepDigit f coh ≡ 0d
  stepDigit-mid f coh lo hi = selectDigitQuarter-between (q10 f) lo hi

  stepDigit-pos :
    (f : ℚ₊ → 𝟛ᴺ) →
    (coh : ∀ δ ε → stream→ℝ (f δ) ∼[ δ +₊ ε ] stream→ℝ (f ε)) →
    1/4ℚ ℚO.< q10 f →
    stepDigit f coh ≡ +1d
  stepDigit-pos f coh 1/4<q = selectDigitQuarter> (q10 f) 1/4<q

  nextRat-neg-bounds :
    (f : ℚ₊ → 𝟛ᴺ) →
    (coh : ∀ δ ε → stream→ℝ (f δ) ∼[ δ +₊ ε ] stream→ℝ (f ε)) →
    (ε' : ℚ₊) →
    q10 f ℚO.< (ℚP.- 1/4ℚ) →
    ((ℚP.- 1Q) ℚO.≤ stepNextRat f coh ε')
    × (stepNextRat f coh ε' ℚO.< (1Q ℚP.+ fst (twoζ ε')))
  nextRat-neg-bounds f coh ε' q<-1/4 = lo , hi
    where
      g : ℚ.ℚ
      g = stepGetApprox f coh ε'

      d-neg : stepDigit f coh ≡ -1d
      d-neg = stepDigit-neg f coh q<-1/4

      g-lo : (ℚP.- 1Q) ℚO.≤ g
      g-lo = fst (stepGetApprox-interval f coh ε')

      g<q+β : g ℚO.< (q10 f ℚP.+ fst (β ε'))
      g<q+β = getApprox<q10+β f coh ε'

      q+β<ζ : (q10 f ℚP.+ fst (β ε')) ℚO.< fst (ζ ε')
      q+β<ζ =
        subst2
          ℚO._<_
          (ℚ!!)
          (ℚ!!)
          (plus-right-< (q10 f) (ℚP.- 1/4ℚ) (fst (β ε')) q<-1/4)

      g<ζ : g ℚO.< fst (ζ ε')
      g<ζ = ℚO.isTrans< g (q10 f ℚP.+ fst (β ε')) (fst (ζ ε')) g<q+β q+β<ζ

      x-def : stepNextRat f coh ε' ≡ ((2Q ℚP.· g) ℚP.+ 1Q)
      x-def =
        stepNextRat f coh ε'
          ≡⟨ cong (λ d → (2Q ℚP.· g) ℚP.- digitToℚ d) d-neg ⟩
        (2Q ℚP.· g) ℚP.- digitToℚ -1d
          ≡⟨ expr--1d g ⟩
        (2Q ℚP.· g) ℚP.+ 1Q
          ∎

      lo-raw : (ℚP.- 1Q) ℚO.≤ ((2Q ℚP.· g) ℚP.+ 1Q)
      lo-raw =
        subst
          (λ t → t ℚO.≤ ((2Q ℚP.· g) ℚP.+ 1Q))
          (ℚ!!)
          (plus-right-≤ (2Q ℚP.· (ℚP.- 1Q)) (2Q ℚP.· g) 1Q (mul2-≤-local g-lo))

      lo : (ℚP.- 1Q) ℚO.≤ stepNextRat f coh ε'
      lo = subst ((ℚP.- 1Q) ℚO.≤_) (sym x-def) lo-raw

      hi-raw : ((2Q ℚP.· g) ℚP.+ 1Q) ℚO.< (1Q ℚP.+ fst (twoζ ε'))
      hi-raw =
        subst2
          ℚO._<_
          refl
          (ℚP.+Comm (2Q ℚP.· fst (ζ ε')) 1Q ∙ ℚ!!)
          (plus-right-< (2Q ℚP.· g) (2Q ℚP.· fst (ζ ε')) 1Q (mul2-<-local g<ζ))

      hi : stepNextRat f coh ε' ℚO.< (1Q ℚP.+ fst (twoζ ε'))
      hi = subst (λ t → t ℚO.< (1Q ℚP.+ fst (twoζ ε'))) (sym x-def) hi-raw

  nextRat-mid-bounds :
    (f : ℚ₊ → 𝟛ᴺ) →
    (coh : ∀ δ ε → stream→ℝ (f δ) ∼[ δ +₊ ε ] stream→ℝ (f ε)) →
    (ε' : ℚ₊) →
    (ℚP.- 1/4ℚ) ℚO.≤ q10 f →
    q10 f ℚO.≤ 1/4ℚ →
    (((ℚP.- 1Q) ℚP.- fst (twoζ ε')) ℚO.< stepNextRat f coh ε')
    × (stepNextRat f coh ε' ℚO.< (1Q ℚP.+ fst (twoζ ε')))
  nextRat-mid-bounds f coh ε' q≥-1/4 q≤1/4 = lo , hi
    where
      g : ℚ.ℚ
      g = stepGetApprox f coh ε'

      d-mid : stepDigit f coh ≡ 0d
      d-mid = stepDigit-mid f coh q≥-1/4 q≤1/4

      g<q+β : g ℚO.< (q10 f ℚP.+ fst (β ε'))
      g<q+β = getApprox<q10+β f coh ε'

      q<g+β : q10 f ℚO.< (g ℚP.+ fst (β ε'))
      q<g+β = q10<getApprox+β f coh ε'

      g<half+ζ : g ℚO.< (inv2^ zero ℚP.+ fst (ζ ε'))
      g<half+ζ =
        ℚO.isTrans<≤ g (q10 f ℚP.+ fst (β ε')) (inv2^ zero ℚP.+ fst (ζ ε')) g<q+β
          (subst2
            ℚO._≤_
            (ℚ!!)
            (ℚ!!)
            (plus-right-≤ (q10 f) 1/4ℚ (fst (β ε')) q≤1/4))

      neg-half-ζ<g : ((ℚP.- inv2^ zero) ℚP.- fst (ζ ε')) ℚO.< g
      neg-half-ζ<g =
        subst2
          ℚO._<_
          (ℚ!!)
          (ℚ!!)
          (plus-right-< (ℚP.- 1/4ℚ) (g ℚP.+ fst (β ε')) (ℚP.- fst (β ε'))
            (ℚO.isTrans≤< (ℚP.- 1/4ℚ) (q10 f) (g ℚP.+ fst (β ε'))
              q≥-1/4
              q<g+β))

      x-def : stepNextRat f coh ε' ≡ (2Q ℚP.· g)
      x-def =
        stepNextRat f coh ε'
          ≡⟨ cong (λ d → (2Q ℚP.· g) ℚP.- digitToℚ d) d-mid ⟩
        (2Q ℚP.· g) ℚP.- digitToℚ 0d
          ≡⟨ expr-0d-local g ⟩
        (2Q ℚP.· g)
          ∎

      lo-raw : ((ℚP.- 1Q) ℚP.- fst (twoζ ε')) ℚO.< (2Q ℚP.· g)
      lo-raw =
        subst2
          ℚO._<_
          (sym (ℚ!!))
          refl
          (mul2-<-local neg-half-ζ<g)

      lo : ((ℚP.- 1Q) ℚP.- fst (twoζ ε')) ℚO.< stepNextRat f coh ε'
      lo = subst (((ℚP.- 1Q) ℚP.- fst (twoζ ε')) ℚO.<_) (sym x-def) lo-raw

      hi-raw : (2Q ℚP.· g) ℚO.< (1Q ℚP.+ fst (twoζ ε'))
      hi-raw =
        subst2
          ℚO._<_
          refl
          (sym (ℚ!!))
          (mul2-<-local g<half+ζ)

      hi : stepNextRat f coh ε' ℚO.< (1Q ℚP.+ fst (twoζ ε'))
      hi = subst (λ t → t ℚO.< (1Q ℚP.+ fst (twoζ ε'))) (sym x-def) hi-raw

  nextRat-pos-bounds :
    (f : ℚ₊ → 𝟛ᴺ) →
    (coh : ∀ δ ε → stream→ℝ (f δ) ∼[ δ +₊ ε ] stream→ℝ (f ε)) →
    (ε' : ℚ₊) →
    1/4ℚ ℚO.< q10 f →
    (((ℚP.- 1Q) ℚP.- fst (twoζ ε')) ℚO.< stepNextRat f coh ε')
    × (stepNextRat f coh ε' ℚO.< (1Q ℚP.+ fst (twoζ ε')))
  nextRat-pos-bounds f coh ε' 1/4<q = lo , hi
    where
      g : ℚ.ℚ
      g = stepGetApprox f coh ε'

      d-pos : stepDigit f coh ≡ +1d
      d-pos = stepDigit-pos f coh 1/4<q

      g-hi : g ℚO.≤ 1Q
      g-hi = snd (stepGetApprox-interval f coh ε')

      q<g+β : q10 f ℚO.< (g ℚP.+ fst (β ε'))
      q<g+β = q10<getApprox+β f coh ε'

      negζ<g : (ℚP.- fst (ζ ε')) ℚO.< g
      negζ<g =
        subst2
          ℚO._<_
          (ℚ!!)
          (ℚ!!)
          (plus-right-< 1/4ℚ (g ℚP.+ fst (β ε')) (ℚP.- fst (β ε'))
            (ℚO.isTrans< 1/4ℚ (q10 f) (g ℚP.+ fst (β ε')) 1/4<q q<g+β))

      x-def : stepNextRat f coh ε' ≡ ((2Q ℚP.· g) ℚP.- 1Q)
      x-def =
        stepNextRat f coh ε'
          ≡⟨ cong (λ d → (2Q ℚP.· g) ℚP.- digitToℚ d) d-pos ⟩
        (2Q ℚP.· g) ℚP.- digitToℚ +1d
          ≡⟨ expr-+1d-local g ⟩
        (2Q ℚP.· g) ℚP.- 1Q
          ∎

      lo-raw : ((ℚP.- 1Q) ℚP.- fst (twoζ ε')) ℚO.< ((2Q ℚP.· g) ℚP.- 1Q)
      lo-raw =
        subst2
          ℚO._<_
          (ℚ!!)
          refl
          (plus-right-< (2Q ℚP.· (ℚP.- fst (ζ ε'))) (2Q ℚP.· g) (ℚP.- 1Q) (mul2-<-local negζ<g))

      lo : ((ℚP.- 1Q) ℚP.- fst (twoζ ε')) ℚO.< stepNextRat f coh ε'
      lo = subst (((ℚP.- 1Q) ℚP.- fst (twoζ ε')) ℚO.<_) (sym x-def) lo-raw

      hi≤1 : ((2Q ℚP.· g) ℚP.- 1Q) ℚO.≤ 1Q
      hi≤1 =
        subst
          (λ t → t ℚO.≤ 1Q)
          (ℚ!!)
          (plus-right-≤ (2Q ℚP.· g) 2Q (ℚP.- 1Q) (mul2-≤-local g-hi))

      hi-raw : ((2Q ℚP.· g) ℚP.- 1Q) ℚO.< (1Q ℚP.+ fst (twoζ ε'))
      hi-raw = ℚO.isTrans≤< ((2Q ℚP.· g) ℚP.- 1Q) 1Q (1Q ℚP.+ fst (twoζ ε')) hi≤1 (1<1+twoζ ε')

      hi : stepNextRat f coh ε' ℚO.< (1Q ℚP.+ fst (twoζ ε'))
      hi = subst (λ t → t ℚO.< (1Q ℚP.+ fst (twoζ ε'))) (sym x-def) hi-raw

  nextRat-band :
    (f : ℚ₊ → 𝟛ᴺ) →
    (coh : ∀ δ ε → stream→ℝ (f δ) ∼[ δ +₊ ε ] stream→ℝ (f ε)) →
    (ε' : ℚ₊) →
    (((ℚP.- 1Q) ℚP.- fst (twoζ ε')) ℚO.< stepNextRat f coh ε')
    × (stepNextRat f coh ε' ℚO.< (1Q ℚP.+ fst (twoζ ε')))
  nextRat-band f coh ε' with q10 f ℚO.≟ (ℚP.- 1/4ℚ)
  ... | ℚO.lt q<-1/4 =
    let
      neg-bnd = nextRat-neg-bounds f coh ε' q<-1/4
      lo≤ : (ℚP.- 1Q) ℚO.≤ stepNextRat f coh ε'
      lo≤ = fst neg-bnd
      hi : stepNextRat f coh ε' ℚO.< (1Q ℚP.+ fst (twoζ ε'))
      hi = snd neg-bnd
      lo : ((ℚP.- 1Q) ℚP.- fst (twoζ ε')) ℚO.< stepNextRat f coh ε'
      lo = ℚO.isTrans<≤ ((ℚP.- 1Q) ℚP.- fst (twoζ ε')) (ℚP.- 1Q) (stepNextRat f coh ε') (-1-twoζ<-1 ε') lo≤
    in lo , hi
  ... | ℚO.eq q=-1/4 =
    nextRat-mid-bounds
      f coh ε'
      (subst ((ℚP.- 1/4ℚ) ℚO.≤_) (sym q=-1/4) (ℚO.isRefl≤ (ℚP.- 1/4ℚ)))
      (<Weaken≤ (q10 f) 1/4ℚ (subst (λ t → t ℚO.< 1/4ℚ) (sym q=-1/4) -1/4<1/4))
  ... | ℚO.gt -1/4<q with q10 f ℚO.≟ 1/4ℚ
  ...   | ℚO.gt 1/4<q = nextRat-pos-bounds f coh ε' 1/4<q
  ...   | ℚO.eq q=1/4 =
    nextRat-mid-bounds
      f coh ε'
      (<Weaken≤ (ℚP.- 1/4ℚ) (q10 f) -1/4<q)
      (subst ((q10 f) ℚO.≤ 1/4ℚ) q=1/4 (ℚO.isRefl≤ 1/4ℚ))
  ...   | ℚO.lt q<1/4 =
    nextRat-mid-bounds
      f coh ε'
      (<Weaken≤ (ℚP.- 1/4ℚ) (q10 f) -1/4<q)
      (<Weaken≤ (q10 f) 1/4ℚ q<1/4)

  clamp-above1 : (x : ℚ.ℚ) → 1Q ℚO.≤ x → clampℚ x ≡ 1Q
  clamp-above1 x 1≤x =
    clampℚ x
      ≡⟨ refl ⟩
    ℚP.max (ℚP.- 1Q) (ℚP.min 1Q x)
      ≡⟨ cong (ℚP.max (ℚP.- 1Q)) (ℚO.≤→min 1Q x 1≤x) ⟩
    ℚP.max (ℚP.- 1Q) 1Q
      ≡⟨ ℚO.≤→max (ℚP.- 1Q) 1Q (<Weaken≤ (ℚP.- 1Q) 1Q -1<1) ⟩
    1Q
      ∎

  clamp-below-1 : (x : ℚ.ℚ) → x ℚO.≤ (ℚP.- 1Q) → clampℚ x ≡ (ℚP.- 1Q)
  clamp-below-1 x x≤-1 =
    clampℚ x
      ≡⟨ refl ⟩
    ℚP.max (ℚP.- 1Q) (ℚP.min 1Q x)
      ≡⟨ cong (ℚP.max (ℚP.- 1Q)) min1x≡x ⟩
    ℚP.max (ℚP.- 1Q) x
      ≡⟨ max≡-1 ⟩
    (ℚP.- 1Q)
      ∎
    where
      x≤1 : x ℚO.≤ 1Q
      x≤1 = ℚO.isTrans≤ x (ℚP.- 1Q) 1Q x≤-1 (<Weaken≤ (ℚP.- 1Q) 1Q -1<1)

      min1x≡x : ℚP.min 1Q x ≡ x
      min1x≡x = ℚP.minComm 1Q x ∙ ℚO.≤→min x 1Q x≤1

      max≡-1 : ℚP.max (ℚP.- 1Q) x ≡ (ℚP.- 1Q)
      max≡-1 = ℚP.maxComm (ℚP.- 1Q) x ∙ ℚO.≤→max x (ℚP.- 1Q) x≤-1

  neg<0-from-pos : (a : ℚ.ℚ) → 0ℚ ℚO.< a → (ℚP.- a) ℚO.< 0ℚ
  neg<0-from-pos a 0<a =
    subst
      ((ℚP.- a) ℚO.<_)
      (ℚ!!)
      (x<x+y (ℚP.- a) a 0<a)

  base-bridge :
    (f : ℚ₊ → 𝟛ᴺ) →
    (coh : ∀ δ ε → stream→ℝ (f δ) ∼[ δ +₊ ε ] stream→ℝ (f ε)) →
    (ε : ℚ₊) →
    rat (digitContrib (stepDigit f coh) zero)
    ∼[ twoInv2₊ zero +₊ (ε +₊ ε) ]
    stream→ℝ (f ε)
  base-bridge f coh ε =
    ∼-monotone≤ bound≤ step123'
    where
      step1 : rat (digitContrib (stepDigit f coh) zero) ∼[ 3/4ℚ₊ ] rat (q10 f)
      step1 = digit-half-to-q10 f

      step2 : rat (q10 f) ∼[ 3/16ℚ₊ ] stream→ℝ (f 1/16ℚ₊)
      step2 = q10-to-baseStream f

      step3 : stream→ℝ (f 1/16ℚ₊) ∼[ 1/16ℚ₊ +₊ ε ] stream→ℝ (f ε)
      step3 = coh 1/16ℚ₊ ε

      step12 :
        rat (digitContrib (stepDigit f coh) zero)
        ∼[ 3/4ℚ₊ +₊ 3/16ℚ₊ ]
        stream→ℝ (f 1/16ℚ₊)
      step12 = triangle∼ step1 step2

      step123-raw :
        rat (digitContrib (stepDigit f coh) zero)
        ∼[ (3/4ℚ₊ +₊ 3/16ℚ₊) +₊ (1/16ℚ₊ +₊ ε) ]
        stream→ℝ (f ε)
      step123-raw = triangle∼ step12 step3

      step123' :
        rat (digitContrib (stepDigit f coh) zero)
        ∼[ twoInv2₊ zero +₊ ε ]
        stream→ℝ (f ε)
      step123' =
        subst
          (λ x → rat (digitContrib (stepDigit f coh) zero) ∼[ x ] stream→ℝ (f ε))
          (ℚ₊≡ ℚ!!)
          step123-raw

      bound≤ : fst (twoInv2₊ zero +₊ ε) ℚO.≤ fst (twoInv2₊ zero +₊ (ε +₊ ε))
      bound≤ = ℚO.≤Monotone+ _ _ _ _ (ℚO.isRefl≤ (fst (twoInv2₊ zero))) (ε≤ε+ε ε)

  clamp-error-from-band :
    (x a : ℚ.ℚ) →
    0ℚ ℚO.< a →
    ((ℚP.- 1Q) ℚP.- a) ℚO.< x →
    x ℚO.< (1Q ℚP.+ a) →
    ℚP.abs (clampℚ x ℚP.- x) ℚO.< a
  clamp-error-from-band x a 0<a lo hi with x ℚO.≟ (ℚP.- 1Q)
  ... | ℚO.lt x<-1 =
    subst
      (λ t → ℚP.abs t ℚO.< a)
      diff-eq
      (bound→abs ((ℚP.- 1Q) ℚP.- x) a lo-bnd hi-bnd)
    where
      x≤-1 : x ℚO.≤ (ℚP.- 1Q)
      x≤-1 = <Weaken≤ x (ℚP.- 1Q) x<-1
  
      clamp=-1 : clampℚ x ≡ (ℚP.- 1Q)
      clamp=-1 = clamp-below-1 x x≤-1
  
      diff-eq : (clampℚ x ℚP.- x) ≡ ((ℚP.- 1Q) ℚP.- x)
      diff-eq = cong (λ t → t ℚP.- x) clamp=-1
  
      x+1<0 : (x ℚP.+ 1Q) ℚO.< 0ℚ
      x+1<0 =
        subst
          (_ ℚO.< 0ℚ)
          (ℚ!!)
          (plus-right-< x (ℚP.- 1Q) 1Q x<-1)
  
      0<neg-x-1 : 0ℚ ℚO.< ((ℚP.- 1Q) ℚP.- x)
      0<neg-x-1 =
        subst
          (0ℚ ℚO.<_)
          (ℚ!!)
          (ℚO.minus-< (x ℚP.+ 1Q) 0ℚ x+1<0)
  
      lo-bnd : (ℚP.- a) ℚO.< ((ℚP.- 1Q) ℚP.- x)
      lo-bnd = ℚO.isTrans< (ℚP.- a) 0ℚ ((ℚP.- 1Q) ℚP.- x) (neg<0-from-pos a 0<a) 0<neg-x-1
  
      lo' : (ℚP.- a) ℚO.< (x ℚP.+ 1Q)
      lo' =
        subst
          (_ ℚO.< (x ℚP.+ 1Q))
          (ℚ!!)
          (plus-right-< (((ℚP.- 1Q) ℚP.- a)) x 1Q lo)
  
      hi-bnd : ((ℚP.- 1Q) ℚP.- x) ℚO.< a
      hi-bnd =
        subst
          (_ ℚO.< a)
          (ℚ!!)
          (ℚO.minus-< (ℚP.- a) (x ℚP.+ 1Q) lo')
  ... | ℚO.eq x=-1 =
    subst
      (λ t → ℚP.abs (clampℚ t ℚP.- t) ℚO.< a)
      x=-1
      at-minus1
    where
      clamp=-1 : clampℚ (ℚP.- 1Q) ≡ (ℚP.- 1Q)
      clamp=-1 = clamp-below-1 (ℚP.- 1Q) (ℚO.isRefl≤ (ℚP.- 1Q))
  
      diff0 : (clampℚ (ℚP.- 1Q) ℚP.- (ℚP.- 1Q)) ≡ 0ℚ
      diff0 = cong (λ t → t ℚP.- (ℚP.- 1Q)) clamp=-1 ∙ ℚ!!
  
      at-minus1 : ℚP.abs (clampℚ (ℚP.- 1Q) ℚP.- (ℚP.- 1Q)) ℚO.< a
      at-minus1 =
        subst
          (λ t → t ℚO.< a)
          (cong ℚP.abs diff0 ∙ ℚ!!)
          0<a
  ... | ℚO.gt -1<x with x ℚO.≟ 1Q
  ...   | ℚO.gt 1<x =
    subst
      (λ t → ℚP.abs t ℚO.< a)
      diff-eq
      (bound→abs (1Q ℚP.- x) a lo-bnd hi-bnd)
    where
      x≥1 : 1Q ℚO.≤ x
      x≥1 = <Weaken≤ 1Q x 1<x
  
      clamp=1 : clampℚ x ≡ 1Q
      clamp=1 = clamp-above1 x x≥1
  
      diff-eq : (clampℚ x ℚP.- x) ≡ (1Q ℚP.- x)
      diff-eq = cong (λ t → t ℚP.- x) clamp=1
  
      x-1<a : (x ℚP.- 1Q) ℚO.< a
      x-1<a =
        subst
          (_ ℚO.< a)
          (ℚ!!)
          (plus-right-< x (1Q ℚP.+ a) (ℚP.- 1Q) hi)
  
      lo-bnd : (ℚP.- a) ℚO.< (1Q ℚP.- x)
      lo-bnd =
        subst
          (_ ℚO.< (1Q ℚP.- x))
          (ℚ!!)
          (ℚO.minus-< (x ℚP.- 1Q) a x-1<a)
  
      0<x-1 : 0ℚ ℚO.< (x ℚP.- 1Q)
      0<x-1 =
        subst
          (_ ℚO.< (x ℚP.- 1Q))
          (ℚ!!)
          (plus-right-< 1Q x (ℚP.- 1Q) 1<x)
  
      1-x<0 : (1Q ℚP.- x) ℚO.< 0ℚ
      1-x<0 =
        subst
          (_ ℚO.< 0ℚ)
          (ℚ!!)
          (ℚO.minus-< 0ℚ (x ℚP.- 1Q) 0<x-1)
  
      hi-bnd : (1Q ℚP.- x) ℚO.< a
      hi-bnd = ℚO.isTrans< (1Q ℚP.- x) 0ℚ a 1-x<0 0<a
  ...   | ℚO.eq x=1 =
    subst
      (λ t → ℚP.abs (clampℚ t ℚP.- t) ℚO.< a)
      x=1
      at-one
    where
      clamp=1 : clampℚ 1Q ≡ 1Q
      clamp=1 = clamp-above1 1Q (ℚO.isRefl≤ 1Q)
  
      diff0 : (clampℚ 1Q ℚP.- 1Q) ≡ 0ℚ
      diff0 = cong (λ t → t ℚP.- 1Q) clamp=1 ∙ ℚ!!
  
      at-one : ℚP.abs (clampℚ 1Q ℚP.- 1Q) ℚO.< a
      at-one =
        subst
          (λ t → t ℚO.< a)
          (cong ℚP.abs diff0 ∙ ℚ!!)
          0<a
  ...   | ℚO.lt x<1 =
    subst
      (λ t → ℚP.abs t ℚO.< a)
      diff0
      (subst
        (λ t → t ℚO.< a)
        (ℚ!!)
        0<a)
    where
      x≥-1 : (ℚP.- 1Q) ℚO.≤ x
      x≥-1 = <Weaken≤ (ℚP.- 1Q) x -1<x
  
      x≤1 : x ℚO.≤ 1Q
      x≤1 = <Weaken≤ x 1Q x<1
  
      clamp=x : clampℚ x ≡ x
      clamp=x = clampℚ-fixed x x≥-1 x≤1
  
      diff0 : (clampℚ x ℚP.- x) ≡ 0ℚ
      diff0 = cong (λ t → t ℚP.- x) clamp=x ∙ ℚ!!
  
  clamp-nextRat-close :
    (f : ℚ₊ → 𝟛ᴺ) →
    (coh : ∀ δ ε → stream→ℝ (f δ) ∼[ δ +₊ ε ] stream→ℝ (f ε)) →
    (ε' : ℚ₊) →
    rat (clampℚ (stepNextRat f coh ε')) ∼[ twoζ ε' ] rat (stepNextRat f coh ε')
  clamp-nextRat-close f coh ε' =
    rat-rat-fromAbs
      (clampℚ (stepNextRat f coh ε'))
      (stepNextRat f coh ε')
      (twoζ ε')
      (clamp-error-from-band
        (stepNextRat f coh ε')
        (fst (twoζ ε'))
        (0<→< (fst (twoζ ε')) (snd (twoζ ε')))
        (fst bnd)
        (snd bnd))
    where
      bnd :
        (((ℚP.- 1Q) ℚP.- fst (twoζ ε')) ℚO.< stepNextRat f coh ε')
        × (stepNextRat f coh ε' ℚO.< (1Q ℚP.+ fst (twoζ ε')))
      bnd = nextRat-band f coh ε'
  
  half-clamp-error :
    (f : ℚ₊ → 𝟛ᴺ) →
    (coh : ∀ δ ε → stream→ℝ (f δ) ∼[ δ +₊ ε ] stream→ℝ (f ε)) →
    (ε' : ℚ₊) →
    rat
      (digitContrib (stepDigit f coh) zero
        ℚP.+ (inv2^ zero ℚP.· clampℚ (stepNextRat f coh ε')))
    ∼[ ζ ε' ]
    rat
      (digitContrib (stepDigit f coh) zero
        ℚP.+ (inv2^ zero ℚP.· stepNextRat f coh ε'))
  half-clamp-error f coh ε' =
    subst
      (λ x →
        rat
          (digitContrib (stepDigit f coh) zero
            ℚP.+ (inv2^ zero ℚP.· clampℚ (stepNextRat f coh ε')))
        ∼[ x ]
        rat
          (digitContrib (stepDigit f coh) zero
            ℚP.+ (inv2^ zero ℚP.· stepNextRat f coh ε')))
      (ℚ₊≡ ℚ!!)
      (affine-half-rat∼
        (stepDigit f coh)
        (twoζ ε')
        (clamp-nextRat-close f coh ε'))

  clamp-bridge :
    (f : ℚ₊ → 𝟛ᴺ) →
    (coh : ∀ δ ε → stream→ℝ (f δ) ∼[ δ +₊ ε ] stream→ℝ (f ε)) →
    (ε' : ℚ₊) →
    rat
      (digitContrib (stepDigit f coh) zero
        ℚP.+ (inv2^ zero ℚP.· clampℚ (stepNextRat f coh ε')))
    ∼[ ζ ε' ]
    rat (stepGetApprox f coh ε')
  clamp-bridge f coh ε' =
    subst
      (λ x →
        rat
          (digitContrib (stepDigit f coh) zero
            ℚP.+ (inv2^ zero ℚP.· clampℚ (stepNextRat f coh ε')))
        ∼[ ζ ε' ]
        rat x)
      step-eq
      (half-clamp-error f coh ε')
    where
      g : ℚ.ℚ
      g = stepGetApprox f coh ε'
  
      step-eq :
        digitContrib (stepDigit f coh) zero
        ℚP.+ (inv2^ zero ℚP.· stepNextRat f coh ε')
        ≡ stepGetApprox f coh ε'
      step-eq = ℚ!!
  
  /16≤/8 : (ε : ℚ₊) → fst (/16₊ ε) ℚO.≤ fst (/8₊ ε)
  /16≤/8 ε =
    subst
      (fst (/16₊ ε) ℚO.≤_)
      (cong fst (/16₊+/16₊≡/8₊ ε))
      (/16≤/16+/16)
    where
      /16≤/16+/16 : fst (/16₊ ε) ℚO.≤ fst (/16₊ ε +₊ /16₊ ε)
      /16≤/16+/16 = ε≤ε+ε (/16₊ ε)
  
  /8≤/4 : (ε : ℚ₊) → fst (/8₊ ε) ℚO.≤ fst (/4₊ ε)
  /8≤/4 ε =
    subst
      (fst (/8₊ ε) ℚO.≤_)
      (cong fst (/8₊+/8₊≡/4₊ ε))
      (/8≤/8+/8)
    where
      /8≤/8+/8 : fst (/8₊ ε) ℚO.≤ fst (/8₊ ε +₊ /8₊ ε)
      /8≤/8+/8 = ε≤ε+ε (/8₊ ε)
  
  ζ≤/4 : (ε : ℚ₊) → fst (ζ ε) ℚO.≤ fst (/4₊ ε)
  ζ≤/4 ε =
    subst
      (_ ℚO.≤ fst (/4₊ ε))
      (cong fst (sym (/8₊+/8₊≡/4₊ ε)))
      (ℚO.≤Monotone+ _ _ _ _
        (ℚO.isRefl≤ (fst (/8₊ ε)))
        (/16≤/8 ε))
  
  ζ-half≤/4 : (ε : ℚ₊) → fst (ζ (/2₊ ε)) ℚO.≤ fst (/4₊ ε)
  ζ-half≤/4 ε =
    ℚO.isTrans≤
      (fst (ζ (/2₊ ε)))
      (fst (/4₊ (/2₊ ε)))
      (fst (/4₊ ε))
      (ζ≤/4 (/2₊ ε))
      (subst
        (_ ℚO.≤ fst (/4₊ ε))
        (sym (cong fst (/2₊∘/4₊≡/8₊ ε)))
        (/8≤/4 ε))

  limA-head-unfold :
    (f : ℚ₊ → 𝟛ᴺ) →
    (coh : ∀ δ ε → stream→ℝ (f δ) ∼[ δ +₊ ε ] stream→ℝ (f ε)) →
    head (limA f coh) ≡ stepDigit f coh
  limA-head-unfold f coh = refl
  
  noninv-bound≤ :
    (ε : ℚ₊) →
    fst (/2₊ ε +₊ (ζ (/2₊ ε) +₊ (ζ (/2₊ ε) +₊ ε)))
    ℚO.≤
    fst (ε +₊ ε)
  noninv-bound≤ ε =
    subst
      (_ ℚO.≤ fst (ε +₊ ε))
      rhs-eq
      step3
    where
      z≤q : fst (ζ (/2₊ ε)) ℚO.≤ fst (/4₊ ε)
      z≤q = ζ-half≤/4 ε
  
      step1 :
        fst (ζ (/2₊ ε) +₊ ε) ℚO.≤ fst (/4₊ ε +₊ ε)
      step1 =
        ℚO.≤Monotone+ _ _ _ _
          z≤q
          (ℚO.isRefl≤ (fst ε))
  
      step2 :
        fst (ζ (/2₊ ε) +₊ (ζ (/2₊ ε) +₊ ε))
        ℚO.≤
        fst (/4₊ ε +₊ (/4₊ ε +₊ ε))
      step2 =
        ℚO.≤Monotone+ _ _ _ _
          z≤q
          step1
  
      step3 :
        fst (/2₊ ε +₊ (ζ (/2₊ ε) +₊ (ζ (/2₊ ε) +₊ ε)))
        ℚO.≤
        fst (/2₊ ε +₊ (/4₊ ε +₊ (/4₊ ε +₊ ε)))
      step3 =
        ℚO.≤Monotone+ _ _ _ _
          (ℚO.isRefl≤ (fst (/2₊ ε)))
          step2
  
      rhs-eq :
        fst (/2₊ ε +₊ (/4₊ ε +₊ (/4₊ ε +₊ ε))) ≡ fst (ε +₊ ε)
      rhs-eq = ℚ!!
  
  approx-limA-gen :
    (f : ℚ₊ → 𝟛ᴺ) →
    (coh : ∀ δ ε → stream→ℝ (f δ) ∼[ δ +₊ ε ] stream→ℝ (f ε)) →
    (n : ℕ) →
    (ε : ℚ₊) →
    rat (approx (limA f coh) n) ∼[ twoInv2₊ n +₊ (ε +₊ ε) ] stream→ℝ (f ε)
  approx-limA-gen f coh zero ε = base-bridge f coh ε
  approx-limA-gen f coh (suc n) ε =
    ∼-monotone≤ final-bound≤ step123
    where
      ε' : ℚ₊
      ε' = /2₊ ε
  
      d : Digit
      d = stepDigit f coh
  
      tailF : ℚ₊ → 𝟛ᴺ
      tailF = stepNextStreams f coh
  
      tailC : ∀ δ γ → stream→ℝ (tailF δ) ∼[ δ +₊ γ ] stream→ℝ (tailF γ)
      tailC = stepNextCoh f coh
  
      Bih : ℚ₊
      Bih = twoInv2₊ n +₊ (ε' +₊ ε')
  
      ih0 :
        rat (approx (limA tailF tailC) n)
        ∼[ Bih ]
        stream→ℝ (tailF ε')
      ih0 = approx-limA-gen tailF tailC n ε'
  
      ih :
        rat (approx (limA tailF tailC) n)
        ∼[ Bih ]
        rat (clampℚ (stepNextRat f coh ε'))
      ih =
        subst
          (λ x → rat (approx (limA tailF tailC) n) ∼[ Bih ] x)
          (next-roundtrip f coh ε')
          ih0
  
      step1-raw :
        rat (digitContrib d zero ℚP.+ (inv2^ zero ℚP.· approx (limA tailF tailC) n))
        ∼[ /2₊ Bih ]
        rat (digitContrib d zero ℚP.+ (inv2^ zero ℚP.· clampℚ (stepNextRat f coh ε')))
      step1-raw = affine-half-rat∼ d Bih ih
  
      lhs-eq :
        approx (limA f coh) (suc n)
        ≡ digitContrib d zero ℚP.+ (inv2^ zero ℚP.· approx (limA tailF tailC) n)
      lhs-eq =
        approx (limA f coh) (suc n)
          ≡⟨ approx-unfold (limA f coh) n ⟩
        digitContrib (head (limA f coh)) zero
          ℚP.+
        (inv2^ zero ℚP.· approx (tail (limA f coh)) n)
          ≡⟨ cong
              (λ t → digitContrib (head (limA f coh)) zero ℚP.+ (inv2^ zero ℚP.· approx t n))
              (limA-tail-unfold f coh) ⟩
        digitContrib (head (limA f coh)) zero
          ℚP.+
        (inv2^ zero ℚP.· approx (limA tailF tailC) n)
          ≡⟨ cong
              (λ h → digitContrib h zero ℚP.+ (inv2^ zero ℚP.· approx (limA tailF tailC) n))
              (limA-head-unfold f coh) ⟩
        digitContrib d zero
          ℚP.+
        (inv2^ zero ℚP.· approx (limA tailF tailC) n)
          ∎
  
      step1 :
        rat (approx (limA f coh) (suc n))
        ∼[ /2₊ Bih ]
        rat (digitContrib d zero ℚP.+ (inv2^ zero ℚP.· clampℚ (stepNextRat f coh ε')))
      step1 =
        subst
          (λ x →
            rat x
            ∼[ /2₊ Bih ]
            rat (digitContrib d zero ℚP.+ (inv2^ zero ℚP.· clampℚ (stepNextRat f coh ε'))))
          lhs-eq
          step1-raw
  
      step2 :
        rat (digitContrib d zero ℚP.+ (inv2^ zero ℚP.· clampℚ (stepNextRat f coh ε')))
        ∼[ ζ ε' ]
        rat (stepGetApprox f coh ε')
      step2 = clamp-bridge f coh ε'
  
      step12 :
        rat (approx (limA f coh) (suc n))
        ∼[ /2₊ Bih +₊ ζ ε' ]
        rat (stepGetApprox f coh ε')
      step12 = triangle∼ step1 step2
  
      step3 :
        rat (stepGetApprox f coh ε')
        ∼[ /8₊ ε' +₊ (/16₊ ε' +₊ ε) ]
        stream→ℝ (f ε)
      step3 = getApprox-close f coh ε' ε
  
      step123-raw :
        rat (approx (limA f coh) (suc n))
        ∼[ (/2₊ Bih +₊ ζ ε') +₊ (/8₊ ε' +₊ (/16₊ ε' +₊ ε)) ]
        stream→ℝ (f ε)
      step123-raw = triangle∼ step12 step3

      budget-eq :
        ((/2₊ Bih +₊ ζ ε') +₊ (/8₊ ε' +₊ (/16₊ ε' +₊ ε)))
        ≡
        ((twoInv2₊ (suc n) +₊ /2₊ ε) +₊ (ζ (/2₊ ε) +₊ (ζ (/2₊ ε) +₊ ε)))
      budget-eq = ℚ₊≡ ℚ!!
  
      step123 :
        rat (approx (limA f coh) (suc n))
        ∼[ (twoInv2₊ (suc n) +₊ /2₊ ε) +₊ (ζ (/2₊ ε) +₊ (ζ (/2₊ ε) +₊ ε)) ]
        stream→ℝ (f ε)
      step123 =
        subst
          (λ x → rat (approx (limA f coh) (suc n)) ∼[ x ] stream→ℝ (f ε))
          budget-eq
          step123-raw
  
      final-bound≤ :
        fst ((twoInv2₊ (suc n) +₊ /2₊ ε) +₊ (ζ (/2₊ ε) +₊ (ζ (/2₊ ε) +₊ ε)))
        ℚO.≤
        fst (twoInv2₊ (suc n) +₊ (ε +₊ ε))
      final-bound≤ =
        ℚO.≤Monotone+ _ _ _ _
          (ℚO.isRefl≤ (fst (twoInv2₊ (suc n))))
          (noninv-bound≤ ε)

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
    ∀ ε → rat (approxℚ₊ (limA f coh) ε) ∼[ ((ε +₊ ε) +₊ ε) +₊ ε ] stream→ℝ (f ε))
  where

  abstract
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

            -- Step 2: rat (approxℚ₊ s (ε/8)) ∼[ε/2] stream→ℝ (f (ε/8))
            -- By the technical lemma approx-limA-close (with 4ε bound)
            approx-to-f : rat (approxℚ₊ s ε/8) ∼[ ((ε/8 +₊ ε/8) +₊ ε/8) +₊ ε/8 ] stream→ℝ (f ε/8)
            approx-to-f = approx-limA-close f coh ε/8

            -- Transport to ε/2: 4·(ε/8) = ε/2
            approx-to-f' : rat (approxℚ₊ s ε/8) ∼[ /2₊ ε ] stream→ℝ (f ε/8)
            approx-to-f' = subst (λ x → rat (approxℚ₊ s ε/8) ∼[ x ] stream→ℝ (f ε/8))
              (ℚ₊≡ ℚ!!) approx-to-f

            -- Step 3: stream→ℝ (f (ε/8)) ∼[ε/8 + ε/8] L = ∼[ε/4]
            -- By 𝕣-lim-self on the family
            f-to-L-raw : stream→ℝ (f ε/8) ∼[ ε/8 +₊ ε/8 ] L
            f-to-L-raw = 𝕣-lim-self (stream→ℝ ∘ f) coh ε/8 ε/8

            f-to-L : stream→ℝ (f ε/8) ∼[ ε/4 ] L
            f-to-L = subst (λ x → stream→ℝ (f ε/8) ∼[ x ] L) (/8₊+/8₊≡/4₊-ε ε) f-to-L-raw

            -- Combine via triangle inequality:
            -- stream→ℝ s ∼[ε/4] rat (approxℚ₊ s ε/8) ∼[ε/2] stream→ℝ (f ε/8) ∼[ε/4] L
            -- Total: ε/4 + ε/2 + ε/4 = ε ✓ (exact, no weakening needed)
            step12 : stream→ℝ s ∼[ ε/4 +₊ /2₊ ε ] stream→ℝ (f ε/8)
            step12 = triangle∼ stream-to-approx approx-to-f'

            ε-total : ℚ₊
            ε-total = (ε/4 +₊ /2₊ ε) +₊ ε/4

            step123 : stream→ℝ s ∼[ ε-total ] L
            step123 = triangle∼ step12 f-to-L

            -- ε/4 + ε/2 + ε/4 = ε (exact)
            sum-eq : ε-total ≡ ε
            sum-eq = ℚ₊≡ ℚ!!

          in subst (λ x → stream→ℝ s ∼[ x ] L) sum-eq step123

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

------------------------------------------------------------------------
-- Proof of the approximation lemma
------------------------------------------------------------------------
--
-- The core approximation lemma relates the n-digit prefix sum of
-- limA f coh to stream→ℝ (f ε). The proof uses ℕ-induction.
--
-- The intended generalized bound has form: 2·inv2^n + 2ε.
-- At n = ℚ₊→ℕ ε, modulus-correct gives inv2^n < ε, so:
--   2·inv2^n + 2ε < 4ε.

-- Proof of the approximation lemma
abstract
  approx-limA-close-proof :
    (f : ℚ₊ → 𝟛ᴺ) →
    (coh : ∀ δ ε → stream→ℝ (f δ) ∼[ δ +₊ ε ] stream→ℝ (f ε)) →
    ∀ ε → rat (approxℚ₊ (limA f coh) ε) ∼[ ((ε +₊ ε) +₊ ε) +₊ ε ] stream→ℝ (f ε)
  approx-limA-close-proof f coh ε =
    ∼-monotone≤ bound-total gen
    where
      nε : ℕ
      nε = ℚ₊→ℕ ε

      gen :
        rat (approxℚ₊ (limA f coh) ε)
        ∼[ twoInv2₊ nε +₊ (ε +₊ ε) ]
        stream→ℝ (f ε)
      gen = approx-limA-gen f coh nε ε

      inv≤ε : inv2^ nε ℚO.≤ fst ε
      inv≤ε = <Weaken≤ (inv2^ nε) (fst ε) (modulus-correct ε)

      twoInv≤2ε : fst (twoInv2₊ nε) ℚO.≤ fst (ε +₊ ε)
      twoInv≤2ε =
        subst
          (_ ℚO.≤ fst (ε +₊ ε))
          (ℚ!!)
          (ℚO.≤Monotone+ _ _ _ _ inv≤ε inv≤ε)

      bound-total :
        fst (twoInv2₊ nε +₊ (ε +₊ ε))
        ℚO.≤
        fst (((ε +₊ ε) +₊ ε) +₊ ε)
      bound-total =
        subst
          (_ ℚO.≤ fst (((ε +₊ ε) +₊ ε) +₊ ε))
          (ℚ!!)
          (ℚO.≤Monotone+ _ _ _ _
            twoInv≤2ε
            (ℚO.isRefl≤ (fst (ε +₊ ε))))

-- Instantiate the Approximation module
open Approximation approx-limA-close-proof public
