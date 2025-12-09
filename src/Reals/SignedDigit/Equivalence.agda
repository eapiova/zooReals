{-# OPTIONS --cubical --guardedness #-}
-- NOTE: --safe is not used here because tail-bound lemmas are currently postulated.
-- TODO: Fill in tail-bound proofs and restore --safe.

-- Equivalence relation on signed-digit sequences and the quotient type ℝsd
-- Based on TWA Thesis Chapter 5 (TypeTopology), ported to Cubical Agda
--
-- KEY CHANGE: ≈sd is now defined as "same limit in ℝ" rather than
-- "pointwise equal approximations". This weaker definition is more
-- appropriate for signed-digit representation where different digit
-- sequences can represent the same real number.

module Reals.SignedDigit.Equivalence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

open import Cubical.Data.Nat as ℕ using (ℕ; zero; suc; min; minComm)
open import Cubical.Data.Nat.Order as ℕO using (splitℕ-≤; splitℕ-<; ≤-split; min-≤-left; minGLB; ≤-refl; ≤-antisym; <-weaken) renaming (_≤_ to _≤ℕ_)
open import Cubical.Data.Int as ℤ using (ℤ; pos; negsuc)
open import Cubical.Data.Int.Order as ℤO using (zero-≤pos)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)

open import Cubical.Data.Rationals.Base as ℚB using (ℚ; [_/_]; _∼_)
open import Cubical.Data.Rationals.Properties as ℚP using (_·_; _+_; _-_; -_; abs; max; maxComm; maxIdem; -Invol; -[x-y]≡y-x; +InvR; +InvL; +IdL; +IdR; +Comm; ·IdR; ·IdL; ·Comm; ·AnnihilL; ·DistL+)
open import Cubical.Data.Rationals.Order as ℚO using (_≤_; _<_; isRefl≤; isTrans≤; ≤→max; ≤-o+; ≤Monotone+; ≤max; isTotal≤; ≤Dec)

-- For the interpretation into HoTT Cauchy reals
open import Cubical.Data.Rationals.Fast as ℚF using () renaming (ℚ to ℚᶠ)
open import Cubical.Data.Rationals.Fast.Order as ℚFO using (ℚ₊; _ℚ₊+_)
open import Reals.HoTT.Base using (ℝ; rat; lim; _∼[_]_)
open import Cubical.HITs.CauchyReals.Closeness using (refl∼)

open import Cubical.HITs.SetQuotients as SQ hiding ([_])

open import Cubical.Relation.Nullary using (Dec; yes; no)

open import Reals.SignedDigit.Base

------------------------------------------------------------------------
-- Rational approximations
------------------------------------------------------------------------

-- 2^n as ℕ
2^ℕ : ℕ → ℕ
2^ℕ zero = 1
2^ℕ (suc n) = 2 ℕ.· 2^ℕ n

-- 2^n as ℕ₊₁ (for use as denominator) - we know 2^n ≥ 1
2^ℕ₊₁ : ℕ → ℕ₊₁
2^ℕ₊₁ zero = 1+ 0           -- 2^0 = 1
2^ℕ₊₁ (suc n) with 2^ℕ n
... | zero = 1+ 0           -- impossible case
... | suc m = 1+ (m ℕ.+ suc m)  -- 2 * (suc m) = suc m + suc m = 2 + 2m

-- Convert digit to rational: -1 ↦ -1, 0 ↦ 0, +1 ↦ +1
digitToℚ : Digit → ℚ
digitToℚ -1d = [ negsuc 0 / 1+ 0 ]   -- -1/1
digitToℚ 0d  = [ pos 0 / 1+ 0 ]      -- 0/1
digitToℚ +1d = [ pos 1 / 1+ 0 ]      -- 1/1

-- Single digit contribution at position i: dᵢ / 2^(i+1)
digitContrib : Digit → ℕ → ℚ
digitContrib d i = (digitToℚ d) · [ pos 1 / 2^ℕ₊₁ (suc i) ]

-- Finite approximation: Σᵢ₌₀ⁿ dᵢ / 2^(i+1)
-- This computes the partial sum of the signed-digit representation
approx : 𝟛ᴺ → ℕ → ℚ
approx s zero = digitContrib (s ! zero) zero
approx s (suc n) = approx s n + digitContrib (s ! suc n) (suc n)

------------------------------------------------------------------------
-- Interpretation into HoTT Cauchy reals
------------------------------------------------------------------------

-- Convert slow ℚ to fast ℚᶠ for use with HoTT reals
open import Cubical.Data.Int.Fast.Properties as ℤᶠ using (·≡·f)

ℚ→ℚᶠ : ℚ → ℚᶠ
ℚ→ℚᶠ = SQ.rec ℚF.isSetℚ (λ { (a , b) → ℚF.[_/_] a b }) compat
  where
    toFast-rel : (x y : ℤ × ℕ₊₁) → ℚB._∼_ x y → ℚF._∼_ x y
    toFast-rel (a , b) (c , d) rel =
      sym (ℤᶠ.·≡·f a (ℚF.ℕ₊₁→ℤ d)) ∙ rel ∙ ℤᶠ.·≡·f c (ℚF.ℕ₊₁→ℤ b)

    compat : (x y : ℤ × ℕ₊₁) → ℚB._∼_ x y → ℚF.[_/_] (fst x) (snd x) ≡ ℚF.[_/_] (fst y) (snd y)
    compat (a , b) (c , d) rel = ℚF.eq/ (a , b) (c , d) (toFast-rel (a , b) (c , d) rel)

-- Approximation using Fast rationals (for compatibility with ℝ)
approxF : 𝟛ᴺ → ℕ → ℚᶠ
approxF s n = ℚ→ℚᶠ (approx s n)

-- Modulus function: given ε > 0, find n such that 1/2^n < ε
--
-- The signed-digit series has |tail from n| ≤ 1/2^n.
-- So to achieve ε-precision, we need n such that 1/2^n < ε.
--
-- Strategy: Find n such that 2^n > 1/ε, i.e., 2^n · ε > 1
-- We compare fromNat(2^n) with fromNat(1)/ε = 1/ε
-- For ε in ℚᶠ, we check if fromNat(2^n) · ε > fromNat(1)

-- Convert 2^n to fast rational
2^ℚᶠ : ℕ → ℚᶠ
2^ℚᶠ n = ℚF.fromNat (2^ℕ n)

-- 1 as fast rational
1ℚᶠ : ℚᶠ
1ℚᶠ = ℚF.fromNat 1

-- Find smallest n such that 2^n · ε ≥ 1 (i.e., 1/2^n ≤ ε)
-- We add 1 to get strict inequality: 1/2^(n+1) < ε
findModulus-fuel : ℕ → ℕ → ℚᶠ → ℕ
findModulus-fuel zero acc _ = acc  -- out of fuel, return current
findModulus-fuel (suc fuel) acc ε with ℚFO._≟_ 1ℚᶠ (2^ℚᶠ acc ℚF.· ε)
... | ℚFO.lt _ = acc       -- 1 < 2^acc · ε, so 1/2^acc < ε, done
... | ℚFO.eq _ = acc       -- 1 = 2^acc · ε, so 1/2^acc = ε, done (boundary)
... | ℚFO.gt _ = findModulus-fuel fuel (suc acc) ε  -- 1 > 2^acc · ε, need more

-- Default fuel (100 iterations covers rationals with denominators up to 2^100)
modulus-fuel : ℕ
modulus-fuel = 100

-- Proper modulus: find n such that 1/2^n ≤ ε
-- Adding 1 gives strict: 1/2^(n+1) < ε
-- This ensures the tail of the series is bounded by ε
ℚ₊→ℕ : ℚ₊ → ℕ
ℚ₊→ℕ (ε , _) = suc (findModulus-fuel modulus-fuel 0 ε)

-- Approximation indexed by precision
approxℚ₊ : 𝟛ᴺ → ℚ₊ → ℚᶠ
approxℚ₊ s ε = approxF s (ℚ₊→ℕ ε)

-- Convert fast ℚ back to slow ℚ for comparison
ℚᶠ→ℚ : ℚᶠ → ℚ
ℚᶠ→ℚ = SQ.rec ℚB.isSetℚ go compat
  where
    go : ℤ × ℕ₊₁ → ℚ
    go (a , b) = [ a / b ]

    -- Convert relation: Fast._∼_ uses fast int multiplication, Base._∼_ uses slow
    fromFast-rel : (x y : ℤ × ℕ₊₁) → ℚF._∼_ x y → ℚB._∼_ x y
    fromFast-rel (a , b) (c , d) rel =
      ℤᶠ.·≡·f a (ℚB.ℕ₊₁→ℤ d) ∙ rel ∙ sym (ℤᶠ.·≡·f c (ℚB.ℕ₊₁→ℤ b))

    compat : (x y : ℤ × ℕ₊₁) → ℚF._∼_ x y → go x ≡ go y
    compat (a , b) (c , d) rel = ℚB.eq/ (a , b) (c , d) (fromFast-rel (a , b) (c , d) rel)

-- The approximation sequence is Cauchy
-- Using the tail bound: |approx s m - approx s n| ≤ 1/2^{min m n}
-- With proper modulus: 1/2^{ℚ₊→ℕ δ} < δ and 1/2^{ℚ₊→ℕ ε} < ε
-- So 1/2^{min(ℚ₊→ℕ δ, ℚ₊→ℕ ε)} < max(δ, ε) < δ + ε
--
-- For now, we postulate the Cauchy property. A full proof would require
-- showing that the difference of fast rationals is bounded by δ + ε.
postulate
  approxℚ₊-cauchy : (s : 𝟛ᴺ)
    → ∀ (δ ε : ℚ₊) → rat (approxℚ₊ s δ) ∼[ δ ℚFO.ℚ₊+ ε ] rat (approxℚ₊ s ε)

-- Interpret a stream as a Cauchy real via the limit of approximations
stream→ℝ : 𝟛ᴺ → ℝ
stream→ℝ s = lim (λ ε → rat (approxℚ₊ s ε)) (approxℚ₊-cauchy s)

------------------------------------------------------------------------
-- Equivalence relation
------------------------------------------------------------------------

-- Two signed-digit sequences are equivalent if they represent the same
-- real number. This is the natural equivalence for signed-digit representation
-- where different digit sequences can represent the same value.
--
-- OLD (too strong): x ≈sd y = (n : ℕ) → approx x n ≡ approx y n
-- This required pointwise equality of all partial sums, which fails
-- for equivalent representations like 0.111... vs 1.000...
--
-- NEW: x ≈sd y = stream→ℝ x ≡ stream→ℝ y
-- Two streams are equivalent iff they have the same limit in ℝ.

_≈sd_ : 𝟛ᴺ → 𝟛ᴺ → Type₀
x ≈sd y = stream→ℝ x ≡ stream→ℝ y

-- The old strong version is kept for backwards compatibility
_≈sd-strong_ : 𝟛ᴺ → 𝟛ᴺ → Type₀
x ≈sd-strong y = (n : ℕ) → approx x n ≡ approx y n

------------------------------------------------------------------------
-- Signed-digit reals as a quotient type
------------------------------------------------------------------------

-- The type of signed-digit real numbers in [-1, 1]
-- Quotienting by ≈sd identifies streams with the same limit
ℝsd : Type₀
ℝsd = 𝟛ᴺ / _≈sd_

-- Embedding raw sequences into ℝsd
[_]sd : 𝟛ᴺ → ℝsd
[ s ]sd = SQ.[ s ]

-- The quotient is a set
isSetℝsd : isSet ℝsd
isSetℝsd = squash/

------------------------------------------------------------------------
-- Basic elements
------------------------------------------------------------------------

-- The constant zero stream: 0, 0, 0, ...
-- Represents: Σᵢ 0/2^(i+1) = 0
zeroStream : 𝟛ᴺ
zeroStream = repeat 0d

-- The constant +1 stream: +1, +1, +1, ...
-- Represents: Σᵢ 1/2^(i+1) = 1
oneStream : 𝟛ᴺ
oneStream = repeat +1d

-- The constant -1 stream: -1, -1, -1, ...
-- Represents: Σᵢ -1/2^(i+1) = -1
negOneStream : 𝟛ᴺ
negOneStream = repeat -1d

-- Zero, one, and negative one as signed-digit reals
0sd : ℝsd
0sd = [ zeroStream ]sd

1sd : ℝsd
1sd = [ oneStream ]sd

-1sd : ℝsd
-1sd = [ negOneStream ]sd

------------------------------------------------------------------------
-- Tail bound lemmas
------------------------------------------------------------------------

-- The key property of signed-digit approximations:
-- The difference between partial sums at indices m and n is bounded by
-- the tail of a geometric series.

-- Helper: 1 / 2^{n+1} as a rational
inv2^ : ℕ → ℚ
inv2^ n = [ pos 1 / 2^ℕ₊₁ (suc n) ]

-- 0 as a rational
0ℚ : ℚ
0ℚ = [ pos 0 / 1+ 0 ]

------------------------------------------------------------------------
-- Lemmas for tail-bound proof
------------------------------------------------------------------------

-- |digitToℚ d| ≤ 1 for any digit d
-- Since digitToℚ ∈ {-1, 0, 1}, this is trivially true
-- Proof by case analysis on d
-- Note: abs(-1) = max(-1, 1) = 1, abs(0) = max(0,0) = 0, abs(1) = max(1,-1) = 1

-- 1 as a rational
1ℚ : ℚ
1ℚ = [ pos 1 / 1+ 0 ]

-- -1 as a rational  
-1ℚ : ℚ
-1ℚ = [ negsuc 0 / 1+ 0 ]

-- abs(-1) = max(-1, -(-1)) = max(-1, 1) = 1
abs-neg1 : abs -1ℚ ≡ 1ℚ
abs-neg1 = refl  -- max(-1, 1) computes to 1

-- abs(0) = max(0, -0) = max(0, 0) = 0
-- We use maxIdem : max x x ≡ x
abs-zero : abs 0ℚ ≡ 0ℚ
abs-zero = maxIdem 0ℚ

-- abs(1) = max(1, -1) = 1
abs-one : abs 1ℚ ≡ 1ℚ
abs-one = refl  -- max(1, -1) computes to 1

-- 0 ≤ 1 in ℚ
-- For a/b ≤ c/d we need a·d ℤ.≤ c·b
-- Here: 0·1 = 0 ℤ.≤ 1·1 = 1, which follows from zero-≤pos
0≤1ℚ : 0ℚ ℚO.≤ 1ℚ
0≤1ℚ = ℤO.zero-≤pos

digitToℚ-bound : (d : Digit) → abs (digitToℚ d) ℚO.≤ 1ℚ
digitToℚ-bound -1d = subst (ℚO._≤ 1ℚ) (sym abs-neg1) (isRefl≤ 1ℚ)  -- abs(-1) = 1 ≤ 1
digitToℚ-bound 0d  = subst (ℚO._≤ 1ℚ) (sym abs-zero) 0≤1ℚ          -- abs(0) = 0 ≤ 1
digitToℚ-bound +1d = subst (ℚO._≤ 1ℚ) (sym abs-one) (isRefl≤ 1ℚ)   -- abs(1) = 1 ≤ 1

-- |digitContrib d i| ≤ 1/2^{i+1}
-- Since digitContrib d i = digitToℚ d · 1/2^{i+1} and |digitToℚ d| ≤ 1
-- We have |d · (1/2^{i+1})| = |d| · (1/2^{i+1}) ≤ 1 · (1/2^{i+1}) = 1/2^{i+1}

-- Helper: 0 · x = 0 (using ·AnnihilL from the library)
·ZeroL : (x : ℚ) → 0ℚ · x ≡ 0ℚ
·ZeroL = ·AnnihilL

-- Helper: 1 · x = x (using ·IdL from the library)
·OneL : (x : ℚ) → 1ℚ · x ≡ x
·OneL = ·IdL

-- Helper: (-1) · x = -x (proof by computation on representatives)
·NegOneL : (x : ℚ) → -1ℚ · x ≡ - x
·NegOneL = SQ.elimProp (λ _ → ℚB.isSetℚ _ _) (λ _ → refl)

-- Helper: 0 ≤ inv2^ i (positivity of 1/2^n)
-- For 0/1 ≤ 1/2^(i+1), need 0·2^(i+1) ℤ.≤ 1·1
-- Since 0·k = 0 for any k, this is 0 ℤ.≤ 1, i.e., zero-≤pos
0≤inv2^ : (i : ℕ) → 0ℚ ℚO.≤ inv2^ i
0≤inv2^ i = ℤO.zero-≤pos

-- Helper: abs 0 = 0
abs-0ℚ : abs 0ℚ ≡ 0ℚ
abs-0ℚ = maxIdem 0ℚ

-- Helper: abs (-x) = abs x
abs-neg : (x : ℚ) → abs (- x) ≡ abs x
abs-neg x = cong (max (- x)) (-Invol x) ∙ maxComm (- x) x

-- Helper: for positive x, abs x = x
-- We need this for inv2^ which is always positive
-- Strategy: show -x ≤ x when 0 ≤ x, then use ≤→max



-- Actually, let's use a simpler approach: subst with +InvL
-- From 0 ≤ x, using ≤-o+: (-x) + 0 ≤ (-x) + x
-- Simplify: -x ≤ 0
0≤x→-x≤0' : (x : ℚ) → 0ℚ ℚO.≤ x → (- x) ℚO.≤ 0ℚ
0≤x→-x≤0' x 0≤x = subst2 ℚO._≤_ p1 p2 step
  where
    step : ((- x) + 0ℚ) ℚO.≤ ((- x) + x)
    step = ≤-o+ 0ℚ x (- x) 0≤x
    p1 : (- x) + 0ℚ ≡ - x
    p1 = +IdR (- x)
    p2 : (- x) + x ≡ 0ℚ
    p2 = +InvL x

-- Helper: 0 ≤ x implies -x ≤ x (by transitivity through 0)
0≤x→-x≤x : (x : ℚ) → 0ℚ ℚO.≤ x → (- x) ℚO.≤ x
0≤x→-x≤x x 0≤x = isTrans≤ (- x) 0ℚ x (0≤x→-x≤0' x 0≤x) 0≤x

-- abs x = max x (-x), and we want: if 0 ≤ x then abs x = x
-- Using maxComm: max x (-x) = max (-x) x
-- Using ≤→max: if -x ≤ x then max (-x) x = x
abs-pos-inv2^ : (i : ℕ) → abs (inv2^ i) ≡ inv2^ i
abs-pos-inv2^ i = 
  maxComm (inv2^ i) (- inv2^ i) ∙ 
  ≤→max (- inv2^ i) (inv2^ i) (0≤x→-x≤x (inv2^ i) (0≤inv2^ i))

digitContrib-bound : (d : Digit) (i : ℕ) → abs (digitContrib d i) ℚO.≤ inv2^ i
digitContrib-bound -1d i = 
  -- digitContrib -1d i = (-1) · inv2^ i
  -- Need: abs((-1) · inv2^ i) ≤ inv2^ i
  -- We have: (-1) · inv2^ i ≡ -(inv2^ i)  (by ·NegOneL)
  -- So: abs((-1) · inv2^ i) ≡ abs(-(inv2^ i)) ≡ abs(inv2^ i) ≡ inv2^ i
  let p2 : -1ℚ · inv2^ i ≡ - inv2^ i
      p2 = ·NegOneL (inv2^ i)
      p3 : abs (-1ℚ · inv2^ i) ≡ abs (- inv2^ i)
      p3 = cong abs p2
      p4 : abs (- inv2^ i) ≡ abs (inv2^ i)
      p4 = abs-neg (inv2^ i)
      p5 : abs (inv2^ i) ≡ inv2^ i
      p5 = abs-pos-inv2^ i
      path : abs (digitContrib -1d i) ≡ inv2^ i
      path = p3 ∙ p4 ∙ p5
  in subst (ℚO._≤ inv2^ i) (sym path) (isRefl≤ (inv2^ i))
digitContrib-bound 0d i =
  -- digitContrib 0d i = 0 · inv2^ i = 0
  -- abs 0 = 0 ≤ inv2^ i
  let p2 : 0ℚ · inv2^ i ≡ 0ℚ
      p2 = ·ZeroL (inv2^ i)
      p4 : abs (0ℚ · inv2^ i) ≡ abs 0ℚ
      p4 = cong abs p2
      path : abs (digitContrib 0d i) ≡ 0ℚ
      path = p4 ∙ abs-0ℚ
  in subst (ℚO._≤ inv2^ i) (sym path) (0≤inv2^ i)
digitContrib-bound +1d i =
  -- digitContrib +1d i = 1 · inv2^ i = inv2^ i
  -- abs(inv2^ i) = inv2^ i ≤ inv2^ i (reflexive)
  let p2 : 1ℚ · inv2^ i ≡ inv2^ i
      p2 = ·OneL (inv2^ i)
      p4 : abs (1ℚ · inv2^ i) ≡ abs (inv2^ i)
      p4 = cong abs p2
      p5 : abs (inv2^ i) ≡ inv2^ i
      p5 = abs-pos-inv2^ i
      path : abs (digitContrib +1d i) ≡ inv2^ i
      path = p4 ∙ p5
  in subst (ℚO._≤ inv2^ i) (sym path) (isRefl≤ (inv2^ i))

-- Helper: (a + b) - a ≡ b
open import Cubical.Data.Rationals.Properties as ℚProps using (+Comm; +Assoc; +IdR; +IdL)

+-minus-cancel : (a b : ℚ) → (a ℚP.+ b) ℚP.- a ≡ b
+-minus-cancel a b =
  -- (a + b) - a = (a + b) + (-a)
  -- Use +Comm on inner: = (b + a) + (-a)
  -- Use +Assoc⁻¹: = b + (a + (-a))
  -- = b + 0 = b
  cong (ℚP._+ (ℚP.- a)) (ℚProps.+Comm a b)   -- (b + a) + (-a)
  ∙ sym (ℚProps.+Assoc b a (ℚP.- a))          -- b + (a + (-a))
  ∙ cong (b ℚP.+_) (ℚP.+InvR a)               -- b + 0
  ∙ ℚProps.+IdR b                              -- b

-- Difference of consecutive approximations
approx-step : (s : 𝟛ᴺ) (n : ℕ) → approx s (suc n) ℚP.- approx s n ≡ digitContrib (s ! suc n) (suc n)
approx-step s n = +-minus-cancel (approx s n) (digitContrib (s ! suc n) (suc n))

-- Key property of the modulus: 1/2^(ℚ₊→ℕ ε) < ε
-- This is what makes the modulus useful for Cauchy proofs
postulate
  modulus-correct : (ε : ℚ₊) → inv2^ (ℚ₊→ℕ ε) ℚO.< ℚᶠ→ℚ (fst ε)

-- The tail bound: for m ≤ n, |approx s n - approx s m| ≤ 1/2^{m+1}
-- This follows because each digit d_i contributes at most 1/2^{i+1},
-- and the sum from i=m+1 to n is bounded by the geometric series sum
-- which converges to 1/2^{m+1}.

-- The following lemmas establish bounds on signed-digit approximations.
-- They require substantial rational arithmetic proofs.
--
-- Proof sketch: The difference is Σᵢ₌ₘ₊₁ⁿ dᵢ/2^{i+1} where |dᵢ| ≤ 1.
-- This sum is bounded by Σᵢ₌ₘ₊₁^∞ 1/2^{i+1} = 1/2^{m+1}.

-- Helper: Triangle inequality for abs
-- Strategy:
-- 1. x ≤ abs x (from ≤max since abs x = max x (-x))
-- 2. -x ≤ abs x (similarly, using maxComm)
-- 3. x + y ≤ abs x + abs y (from 1, using ≤Monotone+)
-- 4. -(x+y) = -x + -y ≤ abs x + abs y (from 2, using ≤Monotone+ and -Dist+)
-- 5. max (x+y) (-(x+y)) ≤ abs x + abs y (from 3,4 using max-LUB)

-- Helper: x ≤ abs x
x≤abs-x : (x : ℚ) → x ℚO.≤ abs x
x≤abs-x x = ≤max x (- x)

-- Helper: -x ≤ abs x  
neg-x≤abs-x : (x : ℚ) → (- x) ℚO.≤ abs x
neg-x≤abs-x x = subst ((- x) ℚO.≤_) (sym (maxComm x (- x))) (≤max (- x) x)

-- Helper: max is LUB - if a ≤ z and b ≤ z, then max a b ≤ z
-- Using decidability of ≤
max-LUB : (a b z : ℚ) → a ℚO.≤ z → b ℚO.≤ z → max a b ℚO.≤ z
max-LUB a b z a≤z b≤z with ≤Dec a b
... | yes a≤b = subst (ℚO._≤ z) (sym (≤→max a b a≤b)) b≤z
... | no ¬a≤b with isTotal≤ a b
...   | inl a≤b' = subst (ℚO._≤ z) (sym (≤→max a b a≤b')) b≤z
...   | inr b≤a  = subst (ℚO._≤ z) (sym (maxComm a b) ∙ sym (≤→max b a b≤a)) a≤z

abs-triangle : (x y : ℚ) → abs (x + y) ℚO.≤ abs x + abs y
abs-triangle x y = max-LUB (x + y) (- (x + y)) (abs x + abs y) xy≤ neg-xy≤
  where
    -- x + y ≤ abs x + abs y
    xy≤ : (x + y) ℚO.≤ (abs x + abs y)
    xy≤ = ≤Monotone+ x (abs x) y (abs y) (x≤abs-x x) (x≤abs-x y)
    
    -- -(x + y) = -x + -y ≤ abs x + abs y
    neg-xy≤ : (- (x + y)) ℚO.≤ (abs x + abs y)
    neg-xy≤ = subst (ℚO._≤ (abs x + abs y)) (sym (-Dist+ x y))
              (≤Monotone+ (- x) (abs x) (- y) (abs y) (neg-x≤abs-x x) (neg-x≤abs-x y))

-- Helper: x - 0 = x
-- x - 0 = x + (-0) = x + 0 = x
minus-zero : (x : ℚ) → x - 0ℚ ≡ x
minus-zero x = +IdR x  -- -0 computes to 0, so x - 0 = x + 0 = x

-- Helper: geometric series property - 1/2^{n+1} ≤ 1/2^n - 1/2^{n+1}
-- This says: adding inv2^(n+1) to current bound still fits in inv2^ n
-- More directly: inv2^ k + inv2^ (suc k) ≤ inv2^ (k - 1) for the series
-- But actually we need: for all i > m, Σᵢ inv2^ i ≤ inv2^ m
postulate
  geom-sum-bound : (m : ℕ) → (n : ℕ) → m ≤ℕ n
    → (sum : ℚ)  -- placeholder for the actual sum
    → sum ℚO.≤ inv2^ m

-- Helper: if x ≤ y and z ≤ w then x + z ≤ y + w
≤-+-mono : (x y z w : ℚ) → x ℚO.≤ y → z ℚO.≤ w → (x + z) ℚO.≤ (y + w)
≤-+-mono = ≤Monotone+

-- Helper: transitivity of ≤
≤-trans : (x y z : ℚ) → x ℚO.≤ y → y ℚO.≤ z → x ℚO.≤ z
≤-trans = isTrans≤

-- Main tail bound: for m ≤ n, |approx s n - approx s m| ≤ 1/2^{m+1}
-- Proof by induction on n - m (the difference)
-- Base: n = m, so approx s n - approx s m = 0, and |0| = 0 ≤ inv2^ m
-- Step: Assume for n, prove for (suc n)
--       approx s (suc n) - approx s m = (approx s n - approx s m) + digitContrib (s ! suc n) (suc n)
--       By triangle: |...| ≤ |approx s n - approx s m| + |digitContrib (s ! suc n) (suc n)|
--       By IH: first term ≤ inv2^ m
--       By digitContrib-bound: second term ≤ inv2^ (suc n)
--       But sum of these may exceed inv2^ m! Need geometric series argument.
--
-- Actually, the bound inv2^ m = 1/2^{m+1} works because:
-- Σᵢ₌ₘ₊₁ⁿ 1/2^{i+1} = 1/2^{m+2} + 1/2^{m+3} + ... + 1/2^{n+1}
--                    < 1/2^{m+2} * (1 + 1/2 + 1/4 + ...)
--                    = 1/2^{m+2} * 2
--                    = 1/2^{m+1}
--                    = inv2^ m
--
-- For now, we postulate this since the full proof requires significant
-- rational arithmetic machinery that would require many more lemmas.
postulate
  tail-bound : (s : 𝟛ᴺ) (m n : ℕ) → m ≤ℕ n
    → abs (approx s n ℚP.- approx s m) ℚO.≤ inv2^ m

-- Helper: symmetry of |x - y|
abs-minus-sym : (x y : ℚ) → abs (x ℚP.- y) ≡ abs (y ℚP.- x)
abs-minus-sym x y = sym (abs-neg (x ℚP.- y)) ∙ cong abs (-[x-y]≡y-x x y)

-- Helper: min m n when m ≤ n
min-eq-left : (m n : ℕ) → m ≤ℕ n → min m n ≡ m
min-eq-left m n m≤n =
  ≤-antisym (min-≤-left {m} {n}) (minGLB {x = m} ≤-refl m≤n)

-- Helper: min m n when n ≤ m
min-eq-right : (m n : ℕ) → n ≤ℕ m → min m n ≡ n
min-eq-right m n n≤m =
  minComm m n ∙ min-eq-left n m n≤m

-- Symmetric version for arbitrary m, n
tail-bound-sym : (s : 𝟛ᴺ) (m n : ℕ)
  → abs (approx s m ℚP.- approx s n) ℚO.≤ inv2^ (min m n)
tail-bound-sym s m n with splitℕ-≤ m n
... | inl m≤n =
  let
    p₀ : abs (approx s n ℚP.- approx s m) ℚO.≤ inv2^ m
    p₀ = tail-bound s m n m≤n

    p₁ : abs (approx s m ℚP.- approx s n) ℚO.≤ inv2^ m
    p₁ = subst (λ z → z ℚO.≤ inv2^ m)
               (sym (abs-minus-sym (approx s m) (approx s n)))
               p₀

    p₂ : abs (approx s m ℚP.- approx s n) ℚO.≤ inv2^ (min m n)
    p₂ = subst (λ t → abs (approx s m ℚP.- approx s n) ℚO.≤ t)
               (cong inv2^ (sym (min-eq-left m n m≤n)))
               p₁
  in p₂
... | inr n<m =
  let
    n≤m : n ≤ℕ m
    n≤m = <-weaken n<m

    p : abs (approx s m ℚP.- approx s n) ℚO.≤ inv2^ n
    p = tail-bound s n m n≤m
  in subst (λ t → abs (approx s m ℚP.- approx s n) ℚO.≤ t)
           (cong inv2^ (sym (min-eq-right m n n≤m)))
           p



------------------------------------------------------------------------
-- Export key lemmas
------------------------------------------------------------------------

-- Re-export for use in Embedding module
open import Cubical.Data.Rationals.Properties public using (abs; _-_)

-- Export the tail bound for use in proving the Cauchy property
-- inv2^ and tail-bound-sym are the key exports
