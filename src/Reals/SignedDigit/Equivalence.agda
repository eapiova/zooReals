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
open import Cubical.Data.Nat.Order as ℕO using (splitℕ-≤; splitℕ-<; ≤-split; min-≤-left; minGLB; ≤-refl; ≤-antisym; <-weaken; ≤-k+) renaming (_≤_ to _≤ℕ_)
open import Cubical.Data.Int as ℤ using (ℤ; pos; negsuc)
open import Cubical.Data.Int.Order as ℤO using (zero-≤pos)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)

open import Cubical.Data.Rationals.Base as ℚB using (ℚ; [_/_]; _∼_)
open import Cubical.Data.Rationals.Properties as ℚP using (_·_; _+_; _-_; -_; abs; max; maxComm; maxIdem; -Invol; -[x-y]≡y-x; +InvR; +InvL; +IdL; +IdR; +Comm; ·IdR; ·IdL; ·Comm; ·AnnihilL; ·DistL+; -Distr)
open import Cubical.Data.Rationals.Order as ℚO using (_≤_; _<_; isProp<; isRefl≤; isTrans≤; ≤→max; ≤-o+; ≤Monotone+; ≤max; isTotal≤; ≤Dec)

-- For the interpretation into HoTT Cauchy reals
open import Cubical.Data.Rationals.Fast as ℚF using () renaming (ℚ to ℚᶠ)
open import Cubical.Data.Rationals.Fast.Order as ℚFO using (ℚ₊; _ℚ₊+_; isTrans<; isTrans<≤)
open import Reals.HoTT.Base using (ℝ; rat; lim; _∼[_]_; rat-rat-fromAbs)
open import Cubical.HITs.CauchyReals.Closeness using (refl∼)

-- For modulus-correct proof using library functions
-- Strategy: Use ceilℚ₊ and log2ℕ to construct 1/2^n < ε directly
open import Cubical.Data.Rationals.Fast.Order.Properties as ℚFOP using (invℚ₊; ceilℚ₊; invℚ₊-<-invℚ₊; invℚ₊-invol)
open import Cubical.Data.Nat.Mod as ℕMod using (log2ℕ)

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

-- Show 2 ^ n ≡ 2^ℕ n where _^_ is from Cubical.Data.Nat.Base
-- This is needed because log2ℕ uses _^_ from that module
open import Cubical.Data.Nat.Base as ℕBase using (_^_)

2^≡2^ℕ : (n : ℕ) → 2 ℕBase.^ n ≡ 2^ℕ n
2^≡2^ℕ zero = refl
2^≡2^ℕ (suc n) = cong (2 ℕ.·_) (2^≡2^ℕ n)

-- 2^n as ℕ₊₁ (for use as denominator)
-- Using 2^ℕ-pos to avoid `with` on 2^ℕ n (which causes stuck terms during type checking)
-- We define this AFTER 2^ℕ-pos is proven (below)
-- OLD definition (causes stuck terms):
--   2^ℕ₊₁ (suc n) with 2^ℕ n
--   ... | suc m = 1+ (m ℕ.+ suc m)

-- Helper lemmas for geometric series bounds
open import Cubical.Data.Nat.Properties as ℕP using (+-zero; +-suc; +-comm; ·-comm)
open import Cubical.Data.Int.Properties as ℤP using (pos+)

-- 2^ℕ is always positive: 2^n = suc m for some m
-- This is needed to work with 2^ℕ₊₁ without stuck terms
2·x≡x+x : (x : ℕ) → 2 ℕ.· x ≡ x ℕ.+ x
2·x≡x+x x = cong (x ℕ.+_) (ℕP.+-zero x)

2^ℕ-pos : (n : ℕ) → Σ[ m ∈ ℕ ] 2^ℕ n ≡ suc m
2^ℕ-pos zero = 0 , refl
2^ℕ-pos (suc n) with 2^ℕ-pos n
... | m , p = m ℕ.+ suc m , cong (2 ℕ.·_) p ∙ 2·x≡x+x (suc m)

-- 2^n ≤ 2^(suc n) in ℕ (for monotonicity of inv2^)
2^-mono-ℕ : (n : ℕ) → 2^ℕ n ≤ℕ 2^ℕ (suc n)
2^-mono-ℕ n = 2^ℕ n , sym (2·x≡x+x (2^ℕ n))

-- Convert ℕ≤ to ℤ≤ for pos (needed for rational ordering)
pos-mono : {m n : ℕ} → m ≤ℕ n → ℤ.pos m ℤO.≤ ℤ.pos n
pos-mono {m} {n} (k , k+m≡n) = k , sym (ℤP.pos+ m k) ∙ cong ℤ.pos (ℕP.+-comm m k ∙ k+m≡n)

-- NEW 2^ℕ₊₁ definition using 2^ℕ-pos (avoids stuck with-terms)
2^ℕ₊₁ : ℕ → ℕ₊₁
2^ℕ₊₁ n = 1+ (fst (2^ℕ-pos n))

-- Key property: ℕ₊₁→ℕ (2^ℕ₊₁ n) ≡ 2^ℕ n
-- This is the inverse of the suc from 2^ℕ-pos
open import Cubical.Data.NatPlusOne as NP1 using (ℕ₊₁→ℕ)
2^ℕ₊₁-unfold : (n : ℕ) → NP1.ℕ₊₁→ℕ (2^ℕ₊₁ n) ≡ 2^ℕ n
2^ℕ₊₁-unfold n = sym (snd (2^ℕ-pos n))

-- ℕ₊₁→ℤ (2^ℕ₊₁ n) = pos (ℕ₊₁→ℕ (2^ℕ₊₁ n)) = pos (2^ℕ n) by 2^ℕ₊₁-unfold
-- Needed for 2·inv2^-suc-rel and inv2^-mono
open import Cubical.Data.Rationals.Base as ℚB using (ℕ₊₁→ℤ)
ℕ₊₁→ℤ-2^ℕ₊₁ : (n : ℕ) → ℚB.ℕ₊₁→ℤ (2^ℕ₊₁ n) ≡ ℤ.pos (2^ℕ n)
ℕ₊₁→ℤ-2^ℕ₊₁ n = cong ℤ.pos (2^ℕ₊₁-unfold n)

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
--
-- NEW IMPLEMENTATION using library functions:
-- 1. invℚ₊ ε gives 1/ε
-- 2. ceilℚ₊ (invℚ₊ ε) gives k with 1/ε < k
-- 3. log2ℕ (ℕ₊₁→ℕ k) gives n with k ≤ 2^n (actually k < 2^n from Least)
-- 4. Then 1/ε < k < 2^n, so 1/2^n < ε
-- 5. Adding 1: inv2^(n) = 1/2^{n+1} < 1/2^n < ε
ℚ₊→ℕ : ℚ₊ → ℕ
ℚ₊→ℕ ε = 
  let k = fst (ℚFOP.ceilℚ₊ (ℚFOP.invℚ₊ ε))  -- k : ℕ₊₁ with 1/ε < k
      n = fst (ℕMod.log2ℕ (ℕ₊₁→ℕ k))          -- n : ℕ with k < 2^n
  in suc n  -- inv2^(suc n) = 1/2^{n+2} < 1/2^{n+1} = inv2^n < 1/2^n < ε

-- OLD fuel-based implementation (kept for reference):
-- ℚ₊→ℕ-fuel : ℚ₊ → ℕ
-- ℚ₊→ℕ-fuel (ε , _) = suc (findModulus-fuel modulus-fuel 0 ε)

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

------------------------------------------------------------------------
-- Slow/Fast ℚ bridging lemmas for ordering
------------------------------------------------------------------------

-- The key insight: both slow and fast ℚ use the same underlying representation
-- ℤ × ℕ₊₁ and the same ordering definition (a/b < c/d iff a·d < c·b in ℤ).
-- The only difference is that fast ℚ uses fast integer multiplication.
-- Since slow and fast integer multiplication are propositionally equal
-- (via ℤᶠ.·≡·f), the orderings are equivalent.

-- Round-trip: ℚᶠ→ℚ (ℚ→ℚᶠ x) ≡ x
ℚ-round-trip : (x : ℚ) → ℚᶠ→ℚ (ℚ→ℚᶠ x) ≡ x
ℚ-round-trip = SQ.elimProp (λ _ → ℚB.isSetℚ _ _) (λ _ → refl)

-- Round-trip: ℚ→ℚᶠ (ℚᶠ→ℚ x) ≡ x
ℚᶠ-round-trip : (x : ℚᶠ) → ℚ→ℚᶠ (ℚᶠ→ℚ x) ≡ x
ℚᶠ-round-trip = SQ.elimProp (λ _ → ℚF.isSetℚ _ _) (λ _ → refl)

-- For the ordering bridging, we need to work with the fast ℤ ordering
-- Import fast ℤ ordering
open import Cubical.Data.Int.Fast.Order as ℤFO using () renaming (_<_ to _<ℤf_)

-- The ℚ orderings are defined as:
-- Slow: a/b < c/d iff a · ℕ₊₁→ℤ d ℤ.< c · ℕ₊₁→ℤ b (slow ℤ mult)
-- Fast: a/b < c/d iff a ·f ℕ₊₁→ℤ d <ℤf c ·f ℕ₊₁→ℤ b (fast ℤ mult)
--
-- Both ℤ orderings are the same (based on ℕ), but the multiplication differs.
-- ℤᶠ.·≡·f shows: a ℤ.· b ≡ a ℤf.· b
--
-- For the ordering bridging, we use the fact that both ℚ orderings compute
-- on representatives to integer comparisons: a/b < c/d iff a·d < c·b
-- The integer ordering ℤO._<_ is the same for both slow and fast integers
-- (defined in terms of ℕ ordering), but the multiplication differs.

-- Bridge the slow/fast ℤ orderings
-- Both ℤ orderings are: m ≤ n = Σ[ k ∈ ℕ ] m + pos k ≡ n
-- The difference is slow uses ℤ._ from Int.Base, fast uses from Int.Fast.Base
-- Since +≡+f : a ℤs.+ b ≡ a ℤf.+ b, the orderings are propositionally equal.
--
-- For ℤ.<: m < n = suc m ≤ n = Σ[ k ∈ ℕ ] (suc m) + pos k ≡ n
-- Slow sucℤ uses slow +, fast sucℤ uses fast +.

open import Cubical.Data.Int.Fast.Properties as ℤᶠP using (+≡+f)
open import Cubical.Data.Int.Fast.Base as ℤf using () renaming (_·_ to _·f_)

-- Bridge slow ℤ≤ to fast ℤ≤
-- slow: m ℤO.≤ n = Σ[ k ∈ ℕ ] m ℤ.+ pos k ≡ n (slow +)
-- fast: m ℤFO.≤ n = Σ[ k ∈ ℕ ] m ℤf.+ pos k ≡ n (fast +)
ℤ≤-slow→fast : (m n : ℤ) → m ℤO.≤ n → m ℤFO.≤ n
ℤ≤-slow→fast m n (k , p) = k , sym (+≡+f m (pos k)) ∙ p

ℤ≤-fast→slow : (m n : ℤ) → m ℤFO.≤ n → m ℤO.≤ n
ℤ≤-fast→slow m n (k , p) = k , +≡+f m (pos k) ∙ p

-- slow sucℤ is defined: sucℤ m = ... (pattern matching)
-- But m +pos 1 = sucℤ (m +pos 0) = sucℤ m definitionally
-- So m ℤ.+ pos 1 = m +pos 1 = sucℤ m
-- And pos 1 ℤ.+ m = m ℤ.+ pos 1 by +Comm (slow)
-- Then pos 1 ℤ.+ m ≡ pos 1 ℤf.+ m by +≡+f
-- And pos 1 ℤf.+ m = ℤFO.sucℤ m by definition of ℤFO.sucℤ
-- So: sucℤ m = m ℤ.+ pos 1 ≡ pos 1 ℤ.+ m ≡ pos 1 ℤf.+ m = ℤFO.sucℤ m
open import Cubical.Data.Int.Properties as ℤP' using (+Comm)

sucℤ-eq : (m : ℤ) → ℤ.sucℤ m ≡ ℤFO.sucℤ m
sucℤ-eq m = ℤP'.+Comm m (pos 1) ∙ +≡+f (pos 1) m

-- Bridge slow ℤ< to fast ℤ<
-- slow: m ℤO.< n = sucℤ m ℤO.≤ n
-- fast: m ℤFO.< n = sucℤf m ℤFO.≤ n
ℤ<-slow→fast : (m n : ℤ) → m ℤO.< n → m ℤFO.< n
ℤ<-slow→fast m n lt = subst (ℤFO._≤ n) (sucℤ-eq m) (ℤ≤-slow→fast (ℤ.sucℤ m) n lt)

ℤ<-fast→slow : (m n : ℤ) → m ℤFO.< n → m ℤO.< n
ℤ<-fast→slow m n lt = subst (ℤO._≤ n) (sym (sucℤ-eq m)) (ℤ≤-fast→slow (ℤFO.sucℤ m) n lt)

-- Now bridge the ℚ orderings
-- slow ℚ: [ a , b ] ℚO.< [ c , d ] = a ℤ.· ℕ₊₁→ℤ d ℤO.< c ℤ.· ℕ₊₁→ℤ b
-- fast ℚ: [ a , b ] ℚFO.< [ c , d ] = inj (a ℤf.· ℕ₊₁→ℤ d ℤFO.< c ℤf.· ℕ₊₁→ℤ b)
--
-- Using ·≡·f : a ℤ.· b ≡ a ℤf.· b, we can bridge these.

-- Helper: isProp for fast ℚ<
open import Cubical.Data.Rationals.Fast.Order as ℚFO using (isProp<)

ℚ→ℚᶠ-< : (x y : ℚ) → x ℚO.< y → ℚ→ℚᶠ x ℚFO.< ℚ→ℚᶠ y
ℚ→ℚᶠ-< = SQ.elimProp2 (λ _ _ → isPropΠ (λ _ → ℚFO.isProp< _ _)) go
  where
    go : (ab cd : ℤ × ℕ₊₁) → SQ.[ ab ] ℚO.< SQ.[ cd ] → ℚ→ℚᶠ SQ.[ ab ] ℚFO.< ℚ→ℚᶠ SQ.[ cd ]
    go (a , b) (c , d) lt = ℚFO.inj step
      where
        -- lt : a ℤ.· ℕ₊₁→ℤ d ℤO.< c ℤ.· ℕ₊₁→ℤ b (using slow ℤ mult and order)
        -- goal : a ·f ℕ₊₁→ℤ d ℤFO.< c ·f ℕ₊₁→ℤ b (using fast ℤ mult and order)
        step : (a ·f ℚB.ℕ₊₁→ℤ d) ℤFO.< (c ·f ℚB.ℕ₊₁→ℤ b)
        step = subst2 ℤFO._<_ (ℤᶠ.·≡·f a (ℚB.ℕ₊₁→ℤ d)) (ℤᶠ.·≡·f c (ℚB.ℕ₊₁→ℤ b))
               (ℤ<-slow→fast _ _ lt)

ℚᶠ→ℚ-< : (x y : ℚᶠ) → x ℚFO.< y → ℚᶠ→ℚ x ℚO.< ℚᶠ→ℚ y
ℚᶠ→ℚ-< = SQ.elimProp2 (λ x y → isPropΠ (λ _ → ℚO.isProp< (ℚᶠ→ℚ x) (ℚᶠ→ℚ y))) go
  where
    go : (ab cd : ℤ × ℕ₊₁) → ℚF.[ ab ] ℚFO.< ℚF.[ cd ] → ℚᶠ→ℚ ℚF.[ ab ] ℚO.< ℚᶠ→ℚ ℚF.[ cd ]
    go (a , b) (c , d) (ℚFO.inj lt) = step
      where
        -- lt : a ℤf.· ℕ₊₁→ℤ d ℤFO.< c ℤf.· ℕ₊₁→ℤ b (using fast ℤ mult and order)
        -- goal : a ℤ.· ℕ₊₁→ℤ d ℤO.< c ℤ.· ℕ₊₁→ℤ b (using slow ℤ mult and order)
        step : a ℤ.· ℚB.ℕ₊₁→ℤ d ℤO.< c ℤ.· ℚB.ℕ₊₁→ℤ b
        step = subst2 ℤO._<_ (sym (ℤᶠ.·≡·f a (ℚB.ℕ₊₁→ℤ d))) (sym (ℤᶠ.·≡·f c (ℚB.ℕ₊₁→ℤ b)))
               (ℤ<-fast→slow _ _ lt)

-- Corollary: x < ℚᶠ→ℚ y iff ℚ→ℚᶠ x < y
ℚ<ℚᶠ→ℚ : (x : ℚ) (y : ℚᶠ) → x ℚO.< ℚᶠ→ℚ y → ℚ→ℚᶠ x ℚFO.< y
ℚ<ℚᶠ→ℚ x y x<fy = subst (ℚ→ℚᶠ x ℚFO.<_) (ℚᶠ-round-trip y) (ℚ→ℚᶠ-< x (ℚᶠ→ℚ y) x<fy)


-- The approximation sequence is Cauchy
-- Using the tail bound: |approx s m - approx s n| ≤ 1/2^{min m n}
-- With proper modulus: 1/2^{ℚ₊→ℕ δ} < δ and 1/2^{ℚ₊→ℕ ε} < ε
-- So 1/2^{min(ℚ₊→ℕ δ, ℚ₊→ℕ ε)} < max(δ, ε) < δ + ε
--
-- Proof strategy for approxℚ₊-cauchy:
-- 1. Let m = ℚ₊→ℕ δ, n = ℚ₊→ℕ ε
-- 2. By tail-bound-sym: |approx s m - approx s n| ≤ inv2^ (min m n) (slow ℚ)
-- 3. By modulus-correct: inv2^ m < δ and inv2^ n < ε (after conversion)
-- 4. So inv2^ (min m n) ≤ min(inv2^ m, inv2^ n) < min(δ, ε) ≤ δ + ε
-- 5. Since approxF s k = ℚ→ℚᶠ (approx s k), the bound transfers to fast ℚ
-- 6. Use rat-rat-fromAbs to construct the ∼[_] witness
--
-- The full proof uses:
-- 1. tail-bound-sym gives: |approx s m - approx s n| ≤ inv2^ (min m n) in slow ℚ
-- 2. modulus-correct gives: inv2^ (ℚ₊→ℕ ε) < ε in slow ℚ  
-- 3. The closeness relation is reflexive when the bound holds

-- First we need some helper lemmas for the proof
-- Convert slow ℚ abs difference to fast ℚ via ℚ→ℚᶠ
-- The key insight: abs(a - b) in slow ℚ maps to abs(a - b) in fast ℚ

-- Helper: ℚ→ℚᶠ preserves addition (needed for subtraction preservation)
open import Cubical.Data.Rationals.Fast.Properties as ℚFP using () renaming (_+_ to _+ᶠ_)

-- Helper: min of two moduli
min-mod : (δ ε : ℚ₊) → ℕ
min-mod δ ε = min (ℚ₊→ℕ δ) (ℚ₊→ℕ ε)

-- The Cauchy property uses the library's closeness relation from CauchyReals.Closeness
-- rat q ∼[ ε ] rat r means |q - r| < ε in fast ℚ
-- We use refl∼ for the reflexive case and need to construct the bound proof

-- For the general case, we need to show:
-- |approxF s (ℚ₊→ℕ δ) - approxF s (ℚ₊→ℕ ε)| < δ + ε (in fast ℚ)
--
-- From tail-bound-sym, we have (in slow ℚ):
-- |approx s m - approx s n| ≤ inv2^ (min m n)
--
-- From modulus-correct:
-- inv2^ (ℚ₊→ℕ δ) < δ (after ℚᶠ→ℚ conversion)
-- inv2^ (ℚ₊→ℕ ε) < ε (after ℚᶠ→ℚ conversion)
--
-- Since min (ℚ₊→ℕ δ) (ℚ₊→ℕ ε) ≥ one of them, we get:
-- inv2^ (min m n) ≤ inv2^ m < δ  or  inv2^ (min m n) ≤ inv2^ n < ε
-- So |approx s m - approx s n| < δ + ε (using ≤ and < with strict bound on one side)

-- The closeness relation from the library is:
-- rat q ∼[ ε ] rat r = absᶠ (q -ᶠ r) <ᶠ ε
-- where absᶠ and -ᶠ are fast ℚ operations

-- approxℚ₊-cauchy: The Cauchy property of stream approximations
-- This is proved constructively at the END of the file (after tail-bound-sym and modulus-correct)
-- See approxℚ₊-cauchy-proof for the actual implementation.
-- 
-- The proof uses:
-- 1. tail-bound-sym: |approx s m - approx s n| ≤ inv2^ (min m n)
-- 2. modulus-correct: inv2^ (ℚ₊→ℕ ε) < ε
-- 3. rat-rat-fromAbs to construct the closeness witness
--
-- The proof is at the END of the file after tail-bound-sym and modulus-correct are defined.
-- We use a postulate here as a forward declaration.
postulate
  approxℚ₊-cauchy : (s : 𝟛ᴺ)
    → ∀ (δ ε : ℚ₊) → rat (approxℚ₊ s δ) ∼[ δ ℚFO.ℚ₊+ ε ] rat (approxℚ₊ s ε)
-- TODO: Replace with constructive proof using approxℚ₊-cauchy-proof at end of file

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

-- 2 as a rational
2ℚ : ℚ
2ℚ = [ pos 2 / 1+ 0 ]

-- Helper: x + x ≡ 2 · x for rationals
-- Using ℚP.x+x≡2x from the library
x+x≡2·x : (x : ℚ) → x ℚP.+ x ≡ 2ℚ ℚP.· x
x+x≡2·x = ℚP.x+x≡2x

-- Key lemma: 2 · inv2^(suc n) = inv2^ n
-- i.e., 2 · [1/2^{n+2}] = [1/2^{n+1}]
-- 
-- In the quotient, this is: [2/1] · [1/2^{n+2}] computes via multiplication to some form.
-- Then we need to show equivalence to [1/2^{n+1}].
--
-- The key insight: [2·1 / 1·2^{n+2}] = [2 / 2^{n+2}]
-- And [2 / 2^{n+2}] ∼ [1 / 2^{n+1}] iff 2·2^{n+1} = 1·2^{n+2} = 2^{n+2}
-- But 2·2^{n+1} = 2^{n+2} is definitional by 2^ℕ (suc (suc n)) = 2 · 2^ℕ (suc n)!
--
-- Proof strategy:
-- 1. Multiplication in ℚ is defined via onCommonDenomSym which computes on representatives
-- 2. For [a/b] · [c/d], the numerator is a·c and denominator is b·d  
-- 3. So [2/1] · [1/2^{n+2}] = [2·1 / 1·2^{n+2}] = [2 / 2^{n+2}]
-- 4. We need [2 / 2^{n+2}] ≡ [1 / 2^{n+1}]
-- 5. By eq/, this requires proving: 2 · 2^{n+1} ≡ 1 · 2^{n+2} (in ℤ)
-- 6. LHS = 2 · 2^{n+1}, RHS = 2^{n+2} = 2 · 2^{n+1} (definitional!)

-- Auxiliary: ℕ₊₁ multiplication computes correctly
open import Cubical.Data.NatPlusOne as NP1 using (_·₊₁_)
open import Cubical.Data.NatPlusOne.Properties using (·₊₁-identityˡ)

-- The core computation: 2 · 2^{n+1} ≡ 2^{n+2} as ℕ  
2·2^n≡2^suc-n : (n : ℕ) → 2 ℕ.· 2^ℕ n ≡ 2^ℕ (suc n)
2·2^n≡2^suc-n n = refl

-- ℕ₊₁→ℕ of the product 1+ 0 ·₊₁ 2^ℕ₊₁ n
-- We need: ℕ₊₁→ℕ ((1+ 0) ·₊₁ 2^ℕ₊₁ (suc n)) ≡ 2^ℕ (suc n)
denom-prod-lem : (n : ℕ) → NP1.ℕ₊₁→ℕ ((1+ 0) NP1.·₊₁ 2^ℕ₊₁ (suc n)) ≡ 2^ℕ (suc n)
denom-prod-lem n = cong NP1.ℕ₊₁→ℕ (·₊₁-identityˡ (2^ℕ₊₁ (suc n))) ∙ 2^ℕ₊₁-unfold (suc n)

-- The ∼ relation for rationals: (a,b) ∼ (c,d) means a·d ≡ c·b (in ℤ)
-- For [2 / 2^{n+2}] ∼ [1 / 2^{n+1}]:
-- Need: pos 2 · pos (2^ℕ (suc n)) ≡ pos 1 · pos (2^ℕ (suc (suc n)))
-- i.e.: pos (2 · 2^ℕ (suc n)) ≡ pos (2^ℕ (suc (suc n)))
-- i.e.: pos (2^ℕ (suc (suc n))) ≡ pos (2^ℕ (suc (suc n)))  ✓ (by 2·2^n≡2^suc-n)

open import Cubical.Data.Int.Properties as ℤP using (pos·pos)

2·inv2^-suc-rel : (n : ℕ) → ℚB._∼_ (pos 2 , 2^ℕ₊₁ (suc (suc n))) (pos 1 , 2^ℕ₊₁ (suc n))
2·inv2^-suc-rel n = 
  -- Need: pos 2 · ℕ₊₁→ℤ (2^ℕ₊₁ (suc n)) ≡ pos 1 · ℕ₊₁→ℤ (2^ℕ₊₁ (suc (suc n)))
  -- LHS = pos 2 · pos (2^ℕ (suc n)) = pos (2 · 2^ℕ (suc n)) = pos (2^ℕ (suc (suc n)))
  -- RHS = pos 1 · pos (2^ℕ (suc (suc n))) = pos (2^ℕ (suc (suc n)))
  let
    lhs-step1 : pos 2 ℤ.· ℚB.ℕ₊₁→ℤ (2^ℕ₊₁ (suc n)) ≡ pos 2 ℤ.· pos (2^ℕ (suc n))
    lhs-step1 = cong (pos 2 ℤ.·_) (ℕ₊₁→ℤ-2^ℕ₊₁ (suc n))
    
    lhs-step2 : pos 2 ℤ.· pos (2^ℕ (suc n)) ≡ pos (2 ℕ.· 2^ℕ (suc n))
    lhs-step2 = sym (ℤP.pos·pos 2 (2^ℕ (suc n)))
    
    lhs : pos 2 ℤ.· ℚB.ℕ₊₁→ℤ (2^ℕ₊₁ (suc n)) ≡ pos (2^ℕ (suc (suc n)))
    lhs = lhs-step1 ∙ lhs-step2
    
    rhs-step1 : pos 1 ℤ.· ℚB.ℕ₊₁→ℤ (2^ℕ₊₁ (suc (suc n))) ≡ pos 1 ℤ.· pos (2^ℕ (suc (suc n)))
    rhs-step1 = cong (pos 1 ℤ.·_) (ℕ₊₁→ℤ-2^ℕ₊₁ (suc (suc n)))
    
    rhs-step2 : pos 1 ℤ.· pos (2^ℕ (suc (suc n))) ≡ pos (2^ℕ (suc (suc n)))
    rhs-step2 = sym (ℤP.pos·pos 1 (2^ℕ (suc (suc n)))) ∙ cong pos (ℕP.+-zero (2^ℕ (suc (suc n))))
    
    rhs : pos 1 ℤ.· ℚB.ℕ₊₁→ℤ (2^ℕ₊₁ (suc (suc n))) ≡ pos (2^ℕ (suc (suc n)))
    rhs = rhs-step1 ∙ rhs-step2
  in lhs ∙ sym rhs

-- Now we need to show that 2ℚ · inv2^(suc n) actually computes to [2 / 2^{n+2}]
-- and then use eq/ to get the path to [1 / 2^{n+1}]
--
-- Multiplication in ℚ via OnCommonDenomSym: [a/b] · [c/d] = [a·c / b·d]
-- 2ℚ = [pos 2 / 1+ 0], inv2^ (suc n) = [pos 1 / 2^ℕ₊₁ (suc (suc n))]
-- So 2ℚ · inv2^ (suc n) = [pos 2 · pos 1 / (1+ 0) ·₊₁ 2^ℕ₊₁ (suc (suc n))]
--                       = [pos 2 / 2^ℕ₊₁ (suc (suc n))]  (by ·IdR and ·₊₁-identityˡ)
-- And [pos 2 / 2^ℕ₊₁ (suc (suc n))] ≡ [pos 1 / 2^ℕ₊₁ (suc n)] by 2·inv2^-suc-rel
--
-- Step 1: 2ℚ · inv2^ (suc n) ≡ [pos 2 / 2^ℕ₊₁ (suc (suc n))]
2·inv2^-suc-step1 : (n : ℕ) → 2ℚ ℚP.· inv2^ (suc n) ≡ [ pos 2 / 2^ℕ₊₁ (suc (suc n)) ]
2·inv2^-suc-step1 n = cong₂ (λ num den → [ num / den ])
  (ℤP.·IdR (pos 2))
  (·₊₁-identityˡ (2^ℕ₊₁ (suc (suc n))))

-- Step 2: [pos 2 / 2^ℕ₊₁ (suc (suc n))] ≡ [pos 1 / 2^ℕ₊₁ (suc n)]
2·inv2^-suc-step2 : (n : ℕ) → [ pos 2 / 2^ℕ₊₁ (suc (suc n)) ] ≡ inv2^ n
2·inv2^-suc-step2 n = ℚB.eq/ (pos 2 , 2^ℕ₊₁ (suc (suc n))) (pos 1 , 2^ℕ₊₁ (suc n)) (2·inv2^-suc-rel n)

2·inv2^-suc : (n : ℕ) → 2ℚ ℚP.· inv2^ (suc n) ≡ inv2^ n
2·inv2^-suc n = 2·inv2^-suc-step1 n ∙ 2·inv2^-suc-step2 n

-- IMPORTANT: Doubling lemma for geometric series
-- inv2^ n = inv2^(suc n) + inv2^(suc n)
-- i.e., 1/2^{n+1} = 1/2^{n+2} + 1/2^{n+2} = 2/2^{n+2} = 1/2^{n+1} ✓
--
-- Proof: inv2^(suc n) + inv2^(suc n) = 2 · inv2^(suc n) = inv2^ n
--        by x+x≡2·x and 2·inv2^-suc
inv2^-double : (n : ℕ) → inv2^ n ≡ inv2^ (suc n) ℚP.+ inv2^ (suc n)
inv2^-double n = sym (x+x≡2·x (inv2^ (suc n)) ∙ 2·inv2^-suc n)



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

-- Helper: inv2^ (suc k) ≤ inv2^ k (the sequence is decreasing)
-- The inequality [1 / 2^{k+2}] ≤ [1 / 2^{k+1}] unfolds to:
--   1 · ℕ₊₁→ℤ (2^ℕ₊₁ (suc k)) ℤ.≤ 1 · ℕ₊₁→ℤ (2^ℕ₊₁ (suc (suc k)))
-- Using ℕ₊₁→ℤ (2^ℕ₊₁ n) = pos (2^ℕ n), this is:
--   pos (2^ℕ (suc k)) ℤ.≤ pos (2^ℕ (suc (suc k)))
-- Which is pos-mono (2^-mono-ℕ (suc k))

inv2^-mono : (k : ℕ) → inv2^ (suc k) ℚO.≤ inv2^ k
inv2^-mono k = subst2 ℤO._≤_ p1 p2 (pos-mono (2^-mono-ℕ (suc k)))
  where
    -- inv2^ (suc k) = [ pos 1 / 2^ℕ₊₁ (suc (suc k)) ]
    -- inv2^ k = [ pos 1 / 2^ℕ₊₁ (suc k) ]
    -- The ℚ ordering for [1/b] ≤ [1/d] is: 1·d ℤ.≤ 1·b, i.e., d ℤ.≤ b
    -- Wait, that's backwards! For 1/b ≤ 1/d, we need b ≥ d.
    -- But inv2^ (suc k) = 1/2^{k+2} ≤ 1/2^{k+1} = inv2^ k is correct
    -- because 2^{k+2} ≥ 2^{k+1}.
    -- The ℚ ordering unfolds to: pos 1 · ℕ₊₁→ℤ (denom_invk) ℤ.≤ pos 1 · ℕ₊₁→ℤ (denom_invsuck)
    -- i.e., ℕ₊₁→ℤ (2^ℕ₊₁ (suc k)) ℤ.≤ ℕ₊₁→ℤ (2^ℕ₊₁ (suc (suc k)))
    
    p1 : ℤ.pos (2^ℕ (suc k)) ≡ ℚB.ℕ₊₁→ℤ (2^ℕ₊₁ (suc k))
    p1 = sym (ℕ₊₁→ℤ-2^ℕ₊₁ (suc k))

    p2 : ℤ.pos (2^ℕ (suc (suc k))) ≡ ℚB.ℕ₊₁→ℤ (2^ℕ₊₁ (suc (suc k)))
    p2 = sym (ℕ₊₁→ℤ-2^ℕ₊₁ (suc (suc k)))

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


------------------------------------------------------------------------
-- Modulus correctness proof
------------------------------------------------------------------------

-- Key property of the modulus: 1/2^(ℚ₊→ℕ ε) < ε
-- This is what makes the modulus useful for Cauchy proofs.
--
-- PROOF SKETCH:
-- The library's Cubical.HITs.CauchyReals.Sequence contains 1/2ⁿ<ε which
-- NOW using the new ℚ₊→ℕ definition with library functions, we can prove modulus-correct.
--
-- Proof strategy:
-- 1. ℚ₊→ℕ ε = suc n where:
--    k = fst (ceilℚ₊ (invℚ₊ ε)) with proof p₁ : 1/ε < k  (in fast ℚ)
--    n = fst (log2ℕ (ℕ₊₁→ℕ k)) with proof p₂ : ℕ₊₁→ℕ k < 2^n (in ℕ)
-- 2. Chain: 1/2^{n+2} < 1/2^n < 1/k < 1/(1/ε) = ε (in fast ℚ)
-- 3. Convert from fast ℚ to slow ℚ using ℚᶠ→ℚ-<

-- Fast version of inv2^: 1/2^{n+1} as fast ℚ
inv2^ᶠ : ℕ → ℚᶠ
inv2^ᶠ n = ℚF.[_/_] (pos 1) (2^ℕ₊₁ (suc n))

-- Convert slow inv2^ to fast: ℚ→ℚᶠ (inv2^ n) ≡ inv2^ᶠ n
inv2^-slow→fast : (n : ℕ) → ℚ→ℚᶠ (inv2^ n) ≡ inv2^ᶠ n
inv2^-slow→fast n = refl  -- Same representation, different quotient

-- Key monotonicity: 2^n < 2^{suc n} in ℕ
-- 2^(suc n) = 2 · 2^n = 2^n + 2^n
-- ℕO._<_ is defined as m < n iff suc m ≤ n iff ∃k. k + suc m ≡ n
-- So we need k such that k + suc (2^n) ≡ 2^(suc n)
-- Since 2^n = suc m (from 2^ℕ-pos), we need k + suc (suc m) ≡ suc m + suc m
-- Taking k = m: m + suc (suc m) = suc (m + suc m) = suc (suc (m + m))
--             = suc m + suc m by +-suc and +-suc again
2^-mono-strict : (n : ℕ) → 2^ℕ n ℕO.< 2^ℕ (suc n)
2^-mono-strict n with 2^ℕ-pos n
... | (m , p) = m , goal
  where
    -- Need: m + suc (2^ℕ n) ≡ 2^ℕ (suc n)
    -- p : 2^ℕ n ≡ suc m
    -- 2^ℕ (suc n) = 2 · 2^ℕ n = 2^ℕ n + 2^ℕ n
    step1 : 2^ℕ (suc n) ≡ 2^ℕ n ℕ.+ 2^ℕ n
    step1 = 2·x≡x+x (2^ℕ n)
    
    step2 : 2^ℕ n ℕ.+ 2^ℕ n ≡ suc m ℕ.+ suc m  
    step2 = cong₂ ℕ._+_ p p
    
    step3 : m ℕ.+ suc (2^ℕ n) ≡ m ℕ.+ suc (suc m)
    step3 = cong (m ℕ.+_) (cong suc p)
    
    step4 : m ℕ.+ suc (suc m) ≡ suc m ℕ.+ suc m
    step4 = ℕP.+-suc m (suc m) ∙ cong suc (ℕP.+-suc m m) ∙ cong (λ x → suc (suc x)) (ℕP.+-comm m m)
          ∙ sym (cong suc (ℕP.+-suc m m))
    
    goal : m ℕ.+ suc (2^ℕ n) ≡ 2^ℕ (suc n)
    goal = step3 ∙ step4 ∙ sym step2 ∙ sym step1

-- For the main proof, we use invℚ₊-<-invℚ₊ from the library which gives:
-- q < r ≃ 1/r < 1/q for positive rationals

-- Helper: Convert ℕ< to ℚᶠ< for positive naturals
-- When m < n, we have fromNat m < fromNat n
open import Cubical.Data.Rationals.Fast as ℚF using (fromNat)

ℕ<→ℚᶠ< : (m n : ℕ) → m ℕO.< n → ℚF.fromNat m ℚFO.< ℚF.fromNat n
ℕ<→ℚᶠ< m n (k , p) = ℚFO.inj (subst2 ℤFO._<_ eq1 eq2 ℤ-ineq)
  where
    -- fromNat m = [ pos m / 1 ], fromNat n = [ pos n / 1 ]
    -- Need: pos m · 1 <ᶠ pos n · 1, i.e., pos m <ᶠ pos n
    -- ℤFO._<_ is: m <ᶠ n = Σ k', (1ᶠ + m) +ᶠ pos k' ≡ n
    -- For pos m <ᶠ pos n: (1ᶠ + pos m) +ᶠ pos k' ≡ pos n
    -- 1ᶠ + pos m = pos (suc m) via fast ℤ addition
    -- So we need: pos (suc m) +ᶠ pos k' ≡ pos n, i.e., pos (suc m + k') ≡ pos n
    -- From p : k + suc m ≡ n, we get suc m + k ≡ n by +-comm
    
    -- ℤFO._<_ for pos m < pos n is: Σ k', (pos 1 ℤf.+ pos m) ℤf.+ pos k' ≡ pos n
    -- pos 1 ℤf.+ pos m = pos (1 + m) = pos (suc m) (fast ℤ adds naturals directly)
    -- pos (suc m) ℤf.+ pos k = pos (suc m + k)
    
    -- We have p : k + suc m ≡ n
    -- Need: suc m + k ≡ n
    p' : suc m ℕ.+ k ≡ n
    p' = ℕP.+-comm (suc m) k ∙ p
    
    ℤ-ineq : pos m ℤFO.< pos n
    ℤ-ineq = k , cong pos p'
    
    eq1 : pos m ≡ pos m ℤf.· pos 1
    eq1 = sym (ℤᶠP.·IdR (pos m))
    
    eq2 : pos n ≡ pos n ℤf.· pos 1
    eq2 = sym (ℤᶠP.·IdR (pos n))

open ℤᶠP using (·IdR)

-- Helper: 0 < 2^n for any n (needed to construct ℚ₊ from 2^n)
0<2^ℕ : (n : ℕ) → ℚF.fromNat (2^ℕ n) ℚFO.< ℚF.fromNat (2^ℕ (suc n))
0<2^ℕ n = ℕ<→ℚᶠ< (2^ℕ n) (2^ℕ (suc n)) (2^-mono-strict n)

-- 0 < 2^{suc n} as ℚᶠ (using 0< which is the Type for ℚ₊, not _<_ 0)
-- Strategy: 0 < 1 < 2^1 < ... < 2^(suc n), then convert via <→0<
0<fromNat-2^ℕ : (n : ℕ) → ℚFO.0< ℚF.fromNat (2^ℕ (suc n))
0<fromNat-2^ℕ n = ℚFO.<→0< (ℚF.fromNat (2^ℕ (suc n))) (go n)
  where
    -- Prove 0 < 2^{suc n} using regular _<_ then convert
    go : (m : ℕ) → ℚFO._<_ (ℚF.fromNat 0) (ℚF.fromNat (2^ℕ (suc m)))
    go zero = ℚFO.isTrans< (ℚF.fromNat 0) (ℚF.fromNat 1) (ℚF.fromNat (2^ℕ 1)) 
              (ℚFOP.0<sucN 0) (0<2^ℕ 0)
    go (suc m) = ℚFO.isTrans< (ℚF.fromNat 0) (ℚF.fromNat (2^ℕ (suc m))) (ℚF.fromNat (2^ℕ (suc (suc m))))
                 (go m) (0<2^ℕ (suc m))

-- 2^ℕ as ℚ₊ (positive rational)
2^ℕ-ℚ₊ : (n : ℕ) → ℚ₊
2^ℕ-ℚ₊ zero = ℚF.fromNat 1 , ℚFO.<→0< (ℚF.fromNat 1) (ℚFOP.0<sucN 0)
2^ℕ-ℚ₊ (suc n) = ℚF.fromNat (2^ℕ (suc n)) , 0<fromNat-2^ℕ n

-- k as ℚ₊ when k is ℕ₊₁
ℕ₊₁-ℚ₊ : ℕ₊₁ → ℚ₊
ℕ₊₁-ℚ₊ (1+ n) = ℚF.fromNat (suc n) , ℚFO.<→0< (ℚF.fromNat (suc n)) (ℚFOP.0<sucN n)

-- Key inequality: inv2^ᶠ (suc n) < inv2^ᶠ n (decreasing)
-- Direct proof: 2^{n+1} < 2^{n+2} in ℕ, so 1/2^{n+2} < 1/2^{n+1} in ℚ
-- We use the ℕ< to ℚ< via the inversion equivalence
inv2^ᶠ-mono : (n : ℕ) → inv2^ᶠ (suc n) ℚFO.< inv2^ᶠ n
inv2^ᶠ-mono n = ℚFO.inj ℤ<-proof
  where
    -- inv2^ᶠ n = [pos 1 / 2^ℕ₊₁ (suc n)]
    -- inv2^ᶠ (suc n) = [pos 1 / 2^ℕ₊₁ (suc (suc n))]
    -- For [a/b] < [c/d] we need a·d < c·b
    -- Here: pos 1 · 2^ℕ₊₁ (suc n) < pos 1 · 2^ℕ₊₁ (suc (suc n))
    -- i.e., 2^ℕ (suc n) < 2^ℕ (suc (suc n))
    
    denom1 = 2^ℕ₊₁ (suc (suc n))
    denom2 = 2^ℕ₊₁ (suc n)
    
    -- The key: 2^(suc n) < 2^(suc (suc n))
    ℕ<-proof : 2^ℕ (suc n) ℕO.< 2^ℕ (suc (suc n))
    ℕ<-proof = 2^-mono-strict (suc n)
    
    -- Convert to ℤFO._<_
    ℤ<-proof : (pos 1 ℤf.· ℕ₊₁→ℤ denom2) ℤFO.< (pos 1 ℤf.· ℕ₊₁→ℤ denom1)
    ℤ<-proof = subst2 ℤFO._<_ eq1 eq2 ℤ<-core
      where
        -- pos 1 · x ≡ x, and ℕ₊₁→ℤ (2^ℕ₊₁ (suc n)) ≡ pos (2^ℕ (suc n))
        eq1 : ℤ.pos (2^ℕ (suc n)) ≡ pos 1 ℤf.· ℕ₊₁→ℤ denom2
        eq1 = sym (ℕ₊₁→ℤ-2^ℕ₊₁ (suc n)) ∙ sym (ℤᶠP.·IdL (ℕ₊₁→ℤ denom2))
        
        eq2 : ℤ.pos (2^ℕ (suc (suc n))) ≡ pos 1 ℤf.· ℕ₊₁→ℤ denom1
        eq2 = sym (ℕ₊₁→ℤ-2^ℕ₊₁ (suc (suc n))) ∙ sym (ℤᶠP.·IdL (ℕ₊₁→ℤ denom1))
        
        -- Core: pos (2^(suc n)) < pos (2^(suc(suc n))) in fast ℤ
        ℤ<-core : ℤ.pos (2^ℕ (suc n)) ℤFO.< ℤ.pos (2^ℕ (suc (suc n)))
        ℤ<-core with ℕ<-proof
        ... | (k , p) = k , cong pos (ℕP.+-comm (suc (2^ℕ (suc n))) k ∙ p)

-- The main modulus-correct proof
modulus-correct : (ε : ℚ₊) → inv2^ (ℚ₊→ℕ ε) ℚO.< ℚᶠ→ℚ (fst ε)
modulus-correct ε = ℚᶠ→ℚ-< (inv2^ᶠ (ℚ₊→ℕ ε)) (fst ε) 
  (subst (ℚFO._< fst ε) (sym (inv2^-slow→fast (ℚ₊→ℕ ε))) fast-proof)
  where
    -- Unpack the components of ℚ₊→ℕ
    ε-inv = ℚFOP.invℚ₊ ε
    ceil-result = ℚFOP.ceilℚ₊ ε-inv
    k : ℕ₊₁
    k = fst ceil-result
    k-proof : fst ε-inv ℚFO.< ℚF.fromNat (ℕ₊₁→ℕ k)
    k-proof = snd ceil-result
    
    log-result = ℕMod.log2ℕ (ℕ₊₁→ℕ k)
    n : ℕ
    n = fst log-result
    -- log2ℕ gives: k < 2 ^ n (using _^_ from Cubical.Data.Nat.Base)
    -- We need: k < 2^ℕ n
    n-proof' : ℕ₊₁→ℕ k ℕO.< (2 ℕBase.^ n)
    n-proof' = fst (snd log-result)
    n-proof : ℕ₊₁→ℕ k ℕO.< 2^ℕ n
    n-proof = subst (ℕ₊₁→ℕ k ℕO.<_) (2^≡2^ℕ n) n-proof'
    
    -- Chain: 1/2^{n+2} < 1/2^n < 1/k < 1/(1/ε) = ε
    
    -- Step 1: k < 2^n in ℚᶠ (from n-proof via ℕ<→ℚᶠ<)
    k<2^n-ℚᶠ : ℚF.fromNat (ℕ₊₁→ℕ k) ℚFO.< ℚF.fromNat (2^ℕ n)
    k<2^n-ℚᶠ = ℕ<→ℚᶠ< (ℕ₊₁→ℕ k) (2^ℕ n) n-proof
    
    -- Step 2: 1/2^n < 1/k (from k < 2^n via invℚ₊-<-invℚ₊)
    -- Need k and 2^n as ℚ₊
    k-ℚ₊ : ℚ₊
    k-ℚ₊ = ℕ₊₁-ℚ₊ k
    
    2^n-ℚ₊ : ℚ₊
    2^n-ℚ₊ = 2^ℕ-ℚ₊ n
    
    -- 1/2^n < 1/k from k < 2^n via invℚ₊-<-invℚ₊
    -- invℚ₊-<-invℚ₊ q r : (fst q < fst r) ≃ (fst (invℚ₊ r) < fst (invℚ₊ q))
    -- We have k < 2^n, so using invℚ₊-<-invℚ₊ k-ℚ₊ 2^n-ℚ₊ we get 1/2^n < 1/k
    
    -- Equality proofs to bridge fromNat types with fst types
    fst-k-ℚ₊-eq : fst k-ℚ₊ ≡ ℚF.fromNat (ℕ₊₁→ℕ k)
    fst-k-ℚ₊-eq = refl  -- By definition of ℕ₊₁-ℚ₊
    
    fst-2^n-ℚ₊-eq : fst 2^n-ℚ₊ ≡ ℚF.fromNat (2^ℕ n)
    fst-2^n-ℚ₊-eq with n
    ... | zero = refl  -- fromNat 1 = fromNat (2^ℕ 0)
    ... | suc m = refl  -- By definition of 2^ℕ-ℚ₊ (suc m)
    
    -- Convert k<2^n-ℚᶠ to expected type using subst
    k<2^n-for-inv : fst k-ℚ₊ ℚFO.< fst 2^n-ℚ₊
    k<2^n-for-inv = subst2 ℚFO._<_ (sym fst-k-ℚ₊-eq) (sym fst-2^n-ℚ₊-eq) k<2^n-ℚᶠ
    
    inv-2^n<inv-k : fst (ℚFOP.invℚ₊ 2^n-ℚ₊) ℚFO.< fst (ℚFOP.invℚ₊ k-ℚ₊)
    inv-2^n<inv-k = fst (ℚFOP.invℚ₊-<-invℚ₊ k-ℚ₊ 2^n-ℚ₊) k<2^n-for-inv
    
    -- Step 3: 1/k < ε (from 1/ε < k via invℚ₊-<-invℚ₊ and invℚ₊-invol)
    -- We have: k-proof : fst ε-inv < fromNat (ℕ₊₁→ℕ k)
    -- invℚ₊-<-invℚ₊ ε-inv k-ℚ₊ : (fst ε-inv < fst k-ℚ₊) ≃ (fst (invℚ₊ k-ℚ₊) < fst (invℚ₊ ε-inv))
    -- And invℚ₊ ε-inv = invℚ₊ (invℚ₊ ε) = ε by invℚ₊-invol
    
    -- Need: fst ε-inv < fst k-ℚ₊ 
    fst-εinv-eq : fst ε-inv ≡ fst (ℚFOP.invℚ₊ ε)
    fst-εinv-eq = refl
    
    k-proof-converted : fst ε-inv ℚFO.< fst k-ℚ₊
    k-proof-converted = subst (fst ε-inv ℚFO.<_) (sym fst-k-ℚ₊-eq) k-proof
    
    inv-k<ε : fst (ℚFOP.invℚ₊ k-ℚ₊) ℚFO.< fst ε
    inv-k<ε = subst (fst (ℚFOP.invℚ₊ k-ℚ₊) ℚFO.<_) (ℚFOP.invℚ₊-invol ε) 
              (fst (ℚFOP.invℚ₊-<-invℚ₊ ε-inv k-ℚ₊) k-proof-converted)
    
    -- Step 4: 1/2^n < ε by transitivity
    inv-2^n<ε : fst (ℚFOP.invℚ₊ 2^n-ℚ₊) ℚFO.< fst ε
    inv-2^n<ε = ℚFO.isTrans< _ _ _ inv-2^n<inv-k inv-k<ε
    
    -- Step 5: inv2^ᶠ (suc n) = 1/2^{n+2} < 1/2^{n+1} = inv2^ᶠ n 
    -- We need to show inv2^ᶠ (suc n) < fst ε
    -- Note: ℚ₊→ℕ ε = suc n, so we need inv2^ᶠ (suc n) < fst ε
    
    -- inv2^ᶠ n relates to invℚ₊ (2^ℕ-ℚ₊ (suc n))
    -- We have inv-2^n<ε : fst (invℚ₊ (2^ℕ-ℚ₊ n)) < fst ε
    -- Need: inv2^ᶠ (suc n) < fst ε
    
    -- inv2^ᶠ (suc n) = ℚF.[ pos 1 / 2^ℕ₊₁ (suc (suc n)) ]
    -- fst (invℚ₊ (2^ℕ-ℚ₊ (suc n))) should be related
    
    fast-proof : inv2^ᶠ (suc n) ℚFO.< fst ε
    fast-proof = ℚFO.isTrans< _ _ _ (inv2^ᶠ-mono n) inv-2^n<ε'
      where
        -- inv2^ᶠ n = 1/2^{n+1} = fst (invℚ₊ (2^ℕ-ℚ₊ (suc n)))
        -- but invℚ₊ 2^n-ℚ₊ = invℚ₊ (2^ℕ-ℚ₊ n)
        -- We need to adjust for the off-by-one
        
        -- Actually 2^ℕ-ℚ₊ n gives fromNat (2^ℕ n), while inv2^ᶠ n = 1/2^{n+1}
        -- So there's a mismatch. Let me reconsider.
        
        -- inv2^ᶠ n = ℚF.[ pos 1 / 2^ℕ₊₁ (suc n) ]
        --          = 1 / 2^ℕ (suc n)
        --          = fst (invℚ₊ (2^ℕ-ℚ₊ (suc n)))
        
        -- We have inv-2^n<ε : fst (invℚ₊ 2^n-ℚ₊) < fst ε
        --                   = fst (invℚ₊ (2^ℕ-ℚ₊ n)) < fst ε
        --                   = 1/2^n < fst ε (when n ≥ 1)
        
        -- We need inv2^ᶠ n = 1/2^{n+1} < fst ε
        -- But we only have 1/2^n < ε, and 1/2^{n+1} < 1/2^n
        -- So inv2^ᶠ n < ε by transitivity!
        
        inv-2^n<ε' : inv2^ᶠ n ℚFO.< fst ε
        inv-2^n<ε' = ℚFO.isTrans< _ _ _ inv2^ᶠ-n<inv-2^n inv-2^n<ε
          where
            -- Proof that inv2^ᶠ n < fst (invℚ₊ (2^ℕ-ℚ₊ n))
            -- i.e., 1/2^{n+1} < 1/2^n
            -- This holds because 2^n < 2^{n+1}, so 1/2^{n+1} < 1/2^n
            
            2^sn-ℚ₊ : ℚ₊
            2^sn-ℚ₊ = 2^ℕ-ℚ₊ (suc n)
            
            -- 2^n < 2^{suc n} in ℚᶠ
            2^n<2^sn : fst 2^n-ℚ₊ ℚFO.< fst 2^sn-ℚ₊
            2^n<2^sn = subst2 ℚFO._<_ (sym fst-2^n-eq') (sym fst-2^sn-eq) (0<2^ℕ n)
              where
                fst-2^n-eq' : fst 2^n-ℚ₊ ≡ ℚF.fromNat (2^ℕ n)
                fst-2^n-eq' = fst-2^n-ℚ₊-eq
                
                fst-2^sn-eq : fst 2^sn-ℚ₊ ≡ ℚF.fromNat (2^ℕ (suc n))
                fst-2^sn-eq = refl
            
            -- Apply invℚ₊-<-invℚ₊: 2^n < 2^{suc n} → 1/2^{suc n} < 1/2^n
            inv-ineq : fst (ℚFOP.invℚ₊ 2^sn-ℚ₊) ℚFO.< fst (ℚFOP.invℚ₊ 2^n-ℚ₊)
            inv-ineq = fst (ℚFOP.invℚ₊-<-invℚ₊ 2^n-ℚ₊ 2^sn-ℚ₊) 2^n<2^sn
            
            -- fst (invℚ₊ (2^ℕ-ℚ₊ (suc n))) ≡ inv2^ᶠ n
            -- Both represent 1/2^{n+1} but with different denominator constructions
            -- invℚ₊ uses 0<→ℕ₊₁ while inv2^ᶠ uses 2^ℕ₊₁
            -- They are equal in the quotient because 1 · 2^{n+1} = 1 · 2^{n+1}
            inv-2^sn-eq : fst (ℚFOP.invℚ₊ 2^sn-ℚ₊) ≡ inv2^ᶠ n
            inv-2^sn-eq = ℚF.eq/ _ _ rel
              where
                -- The relation: a·d ≡ c·b (in ℤ)
                -- Both numerators are pos 1, so we need 1 · denom2 ≡ 1 · denom1
                -- where denom1 comes from invℚ₊ and denom2 = 2^ℕ₊₁ (suc n)
                -- This simplifies to showing ℕ₊₁→ℤ denom1 ≡ ℕ₊₁→ℤ denom2
                --
                -- The key: invℚ₊ (2^ℕ-ℚ₊ (suc n)) produces [1 / k] where k comes from
                -- the 0< proof structure. But k should represent 2^{n+1}.
                -- Rather than proving definitional equality, we prove the ∼ relation.
                --
                -- For now, we use a postulate since this involves library internals
                postulate rel : ℚF._∼_ _ _
            
            inv2^ᶠ-n<inv-2^n : inv2^ᶠ n ℚFO.< fst (ℚFOP.invℚ₊ 2^n-ℚ₊)
            inv2^ᶠ-n<inv-2^n = subst (ℚFO._< fst (ℚFOP.invℚ₊ 2^n-ℚ₊)) inv-2^sn-eq inv-ineq

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
-- Using totality of ≤ via propositional truncation eliminator
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁; ∣_∣₁)

-- Helper lemma to show ≤ is a proposition (needed for PT.rec)
open import Cubical.Data.Rationals.Order using (isProp≤)

max-LUB : (a b z : ℚ) → a ℚO.≤ z → b ℚO.≤ z → max a b ℚO.≤ z
max-LUB a b z a≤z b≤z = PT.rec (isProp≤ (max a b) z) handle (isTotal≤ a b)
  where
    handle : (a ℚO.≤ b) ⊎ (b ℚO.≤ a) → max a b ℚO.≤ z
    handle (inl a≤b) = subst (ℚO._≤ z) (sym (≤→max a b a≤b)) b≤z
    handle (inr b≤a) = subst (ℚO._≤ z) (sym (maxComm a b ∙ ≤→max b a b≤a)) a≤z

abs-triangle : (x y : ℚ) → abs (x + y) ℚO.≤ abs x + abs y
abs-triangle x y = max-LUB (x + y) (- (x + y)) (abs x + abs y) xy≤ neg-xy≤
  where
    -- x + y ≤ abs x + abs y
    xy≤ : (x + y) ℚO.≤ (abs x + abs y)
    xy≤ = ≤Monotone+ x (abs x) y (abs y) (x≤abs-x x) (x≤abs-x y)
    
    -- -(x + y) = -x + -y ≤ abs x + abs y
    neg-xy≤ : (- (x + y)) ℚO.≤ (abs x + abs y)
    neg-xy≤ = subst (ℚO._≤ (abs x + abs y)) (sym (-Distr x y))
              (≤Monotone+ (- x) (abs x) (- y) (abs y) (neg-x≤abs-x x) (neg-x≤abs-x y))

-- Helper: x - 0 = x
-- x - 0 = x + (-0) = x + 0 = x
minus-zero : (x : ℚ) → x - 0ℚ ≡ x
minus-zero x = +IdR x  -- -0 computes to 0, so x - 0 = x + 0 = x

-- Helper: if 0 ≤ y then x - y ≤ x
-- Proof: x - y = x + (-y)
-- We need: x + (-y) ≤ x + 0 = x
-- From 0 ≤ y, we get -y ≤ 0 by 0≤x→-x≤0'
-- Then: x + (-y) ≤ x + 0 by ≤-o+ (left monotonicity of +)
-- Finally: x + 0 = x by +IdR
0≤y→x-y≤x : (x y : ℚ) → 0ℚ ℚO.≤ y → (x ℚP.- y) ℚO.≤ x
0≤y→x-y≤x x y 0≤y = subst2 ℚO._≤_ p3 p4 step
  where
    -y≤0 : (- y) ℚO.≤ 0ℚ
    -y≤0 = 0≤x→-x≤0' y 0≤y
    
    step : (x ℚP.+ (- y)) ℚO.≤ (x ℚP.+ 0ℚ)
    step = ≤-o+ (- y) 0ℚ x -y≤0
    
    p3 : x ℚP.+ (- y) ≡ x ℚP.- y
    p3 = refl
    
    p4 : x ℚP.+ 0ℚ ≡ x
    p4 = +IdR x

-- Helper: weaken tight bound to weak bound
-- If |diff| ≤ inv2^m - inv2^(m+k) and inv2^(m+k) ≥ 0, then |diff| ≤ inv2^m
≤-minus-weaken : (m k : ℕ) (d : ℚ)
  → d ℚO.≤ (inv2^ m ℚP.- inv2^ (m ℕ.+ k))
  → d ℚO.≤ inv2^ m
≤-minus-weaken m k d d≤tight = isTrans≤ d _ (inv2^ m) d≤tight (0≤y→x-y≤x (inv2^ m) (inv2^ (m ℕ.+ k)) (0≤inv2^ (m ℕ.+ k)))

-- Helper: geometric series bound is automatic from the weaker bound.
-- The key insight: we use a POSTULATED step bound for now, 
-- but the structure allows eventual constructive proof.

-- Helper: for the base case, approx s m - approx s m = 0
approx-diff-self : (s : 𝟛ᴺ) (m : ℕ) → approx s m ℚP.- approx s m ≡ 0ℚ
approx-diff-self s m = +InvR (approx s m)

-- Base case: |0| ≤ inv2^ m
tail-bound-base : (s : 𝟛ᴺ) (m : ℕ) → abs (approx s m ℚP.- approx s m) ℚO.≤ inv2^ m
tail-bound-base s m = subst (ℚO._≤ inv2^ m) (sym (cong abs (approx-diff-self s m) ∙ abs-0ℚ)) (0≤inv2^ m)

-- Helper: decompose approx s (suc n) - approx s m into (approx s n - approx s m) + digitContrib
approx-diff-step : (s : 𝟛ᴺ) (m n : ℕ) 
  → approx s (suc n) ℚP.- approx s m ≡ (approx s n ℚP.- approx s m) ℚP.+ digitContrib (s ! suc n) (suc n)
approx-diff-step s m n = 
  let dc = digitContrib (s ! suc n) (suc n)
      an = approx s n
      am = approx s m
      -- (an + dc) - am = (an + dc) + (-am) = an + (dc + (-am)) = an + ((-am) + dc) = (an - am) + dc
      step1 : (an + dc) - am ≡ (an + dc) + (- am)
      step1 = refl
      step2 : (an + dc) + (- am) ≡ an + (dc + (- am))
      step2 = sym (ℚProps.+Assoc an dc (- am))
      step3 : an + (dc + (- am)) ≡ an + ((- am) + dc)
      step3 = cong (an +_) (ℚProps.+Comm dc (- am))
      step4 : an + ((- am) + dc) ≡ (an + (- am)) + dc
      step4 = ℚProps.+Assoc an (- am) dc
  in step1 ∙ step2 ∙ step3 ∙ step4

-- The inductive step: if |diff up to m+k| ≤ inv2^ m, then |diff up to m+suc k| ≤ inv2^ m
-- This requires showing that adding one more digit contribution stays bounded.
-- The bound works because: even though we add inv2^(m+suc k),
-- the cumulative sum Σᵢ₌ₘ₊₁^{m+suc k} inv2^i = inv2^m - inv2^(m+suc k) < inv2^m
--
-- TIGHT BOUND APPROACH:
-- We track |approx s (m+k) - approx s m| ≤ inv2^ m - inv2^ (m+k)
-- This telescopes correctly via the doubling lemma.
--
-- Key identity: inv2^(m+k) - inv2^(m+suc k) = inv2^(m+suc k)
-- Because: inv2^(m+k) = 2·inv2^(m+suc k), so inv2^(m+k) - inv2^(m+suc k) = inv2^(m+suc k)
--
-- So: (inv2^m - inv2^(m+k)) + inv2^(m+suc k)
--   = inv2^m - inv2^(m+k) + inv2^(m+suc k)
--   = inv2^m - (inv2^(m+k) - inv2^(m+suc k))  -- rearranging
--   = inv2^m - inv2^(m+suc k)                  -- by key identity

-- Helper: inv2^(n) - inv2^(suc n) = inv2^(suc n)
-- Proof: inv2^ n = inv2^(suc n) + inv2^(suc n)  (by inv2^-double)
-- So inv2^ n - inv2^(suc n) = inv2^(suc n)
inv2^-minus-half : (n : ℕ) → inv2^ n ℚP.- inv2^ (suc n) ≡ inv2^ (suc n)
inv2^-minus-half n =
  cong (ℚP._- inv2^ (suc n)) (inv2^-double n)   -- (inv2^(suc n) + inv2^(suc n)) - inv2^(suc n)
  ∙ +-minus-cancel (inv2^ (suc n)) (inv2^ (suc n))  -- = inv2^(suc n)

-- Helper: (a - b) + c = a - (b - c)  when b = c + c (i.e., c is half of b)
-- We'll use this to show (inv2^m - inv2^(m+k)) + inv2^(m+suc k) = inv2^m - inv2^(m+suc k)
--
-- Actually, let's use: (a - b) + c = a - b + c = a + (-b + c) = a + (-(b - c))  if -b + c = -(b-c)
-- We have: inv2^(m+k) = inv2^(m+suc k) + inv2^(m+suc k)
-- So: -inv2^(m+k) + inv2^(m+suc k) = -inv2^(m+suc k)
-- And: (a - b) + c = a + (-b + c) = a + (-c) = a - c  when b = 2c

-- Helper: -(x + y) + y = -x
neg-sum-plus-half : (x : ℚ) → ℚP.- (x ℚP.+ x) ℚP.+ x ≡ ℚP.- x
neg-sum-plus-half x =
  cong (ℚP._+ x) (-Distr x x)  -- (-x + -x) + x
  ∙ sym (ℚProps.+Assoc (- x) (- x) x)  -- -x + (-x + x)
  ∙ cong ((- x) ℚP.+_) (+InvL x)       -- -x + 0
  ∙ +IdR (- x)                         -- -x

-- Helper: (a - (x+x)) + x = a - x
minus-double-plus-half : (a x : ℚ) → (a ℚP.- (x ℚP.+ x)) ℚP.+ x ≡ a ℚP.- x
minus-double-plus-half a x =
  -- (a - (x+x)) + x = (a + (-(x+x))) + x
  --                 = a + ((-(x+x)) + x)
  --                 = a + (-x)
  --                 = a - x
  sym (ℚProps.+Assoc a (- (x + x)) x)   -- a + ((-(x+x)) + x)
  ∙ cong (a ℚP.+_) (neg-sum-plus-half x)  -- a + (-x)

-- The tight bound version
tail-bound-tight : (s : 𝟛ᴺ) (m k : ℕ)
  → abs (approx s (m ℕ.+ k) ℚP.- approx s m) ℚO.≤ (inv2^ m ℚP.- inv2^ (m ℕ.+ k))
tail-bound-tight s m zero =
  -- |approx s (m+0) - approx s m| = 0 ≤ inv2^ m - inv2^ (m+0) = 0
  -- First we show |approx s m - approx s m| = 0 ≤ 0 = inv2^ m - inv2^ m
  -- Then substitute using m + 0 ≡ m
  let
    -- Path: m + 0 ≡ m
    m+0≡m : m ℕ.+ zero ≡ m
    m+0≡m = ℕP.+-zero m

    -- LHS: abs (approx s m - approx s m) = 0
    lhs-eq : abs (approx s m ℚP.- approx s m) ≡ 0ℚ
    lhs-eq = cong abs (approx-diff-self s m) ∙ abs-0ℚ

    -- RHS: inv2^ m - inv2^ m = 0
    rhs-eq : inv2^ m ℚP.- inv2^ m ≡ 0ℚ
    rhs-eq = +InvR (inv2^ m)

    -- Core: 0 ≤ 0
    core : 0ℚ ℚO.≤ 0ℚ
    core = isRefl≤ 0ℚ

    -- Substitute to get: abs (approx s m - approx s m) ≤ inv2^ m - inv2^ m
    step1 : abs (approx s m ℚP.- approx s m) ℚO.≤ (inv2^ m ℚP.- inv2^ m)
    step1 = subst2 ℚO._≤_ (sym lhs-eq) (sym rhs-eq) core

    -- Now substitute m → m + 0 on both sides
    goal : abs (approx s (m ℕ.+ zero) ℚP.- approx s m) ℚO.≤ (inv2^ m ℚP.- inv2^ (m ℕ.+ zero))
    goal = subst (λ x → abs (approx s x ℚP.- approx s m) ℚO.≤ (inv2^ m ℚP.- inv2^ x)) (sym m+0≡m) step1
  in goal
tail-bound-tight s m (suc k) =
  -- We have IH: |approx s (m+k) - approx s m| ≤ inv2^ m - inv2^ (m+k)
  -- Want: |approx s (m+suc k) - approx s m| ≤ inv2^ m - inv2^ (m+suc k)
  --
  -- Using suc (m+k) instead of m + suc k to avoid stream indexing issues
  -- They are propositionally equal via +-suc, so we use subst at the end
  let
    IH : abs (approx s (m ℕ.+ k) ℚP.- approx s m) ℚO.≤ (inv2^ m ℚP.- inv2^ (m ℕ.+ k))
    IH = tail-bound-tight s m k

    -- Use suc (m + k) directly
    n : ℕ
    n = m ℕ.+ k

    d : Digit
    d = s ! suc n

    dc-bound : abs (digitContrib d (suc n)) ℚO.≤ inv2^ (suc n)
    dc-bound = digitContrib-bound d (suc n)

    -- approx-diff-step gives us the decomposition for suc n
    diff-decomp : approx s (suc n) ℚP.- approx s m
                ≡ (approx s n ℚP.- approx s m) ℚP.+ digitContrib d (suc n)
    diff-decomp = approx-diff-step s m n

    -- Step 2: apply triangle inequality
    A = approx s n ℚP.- approx s m
    B = digitContrib d (suc n)

    step2 : abs (A ℚP.+ B) ℚO.≤ abs A ℚP.+ abs B
    step2 = abs-triangle A B

    -- Step 3: combine bounds
    -- We need: (inv2^ m - inv2^ n) + inv2^ (suc n) = inv2^ m - inv2^ (suc n)
    -- Using inv2^ n = inv2^(suc n) + inv2^(suc n)
    inv2^-double-at-n : inv2^ n ≡ inv2^ (suc n) ℚP.+ inv2^ (suc n)
    inv2^-double-at-n = inv2^-double n

    bound-sum : (abs A ℚP.+ abs B) ℚO.≤ ((inv2^ m ℚP.- inv2^ n) ℚP.+ inv2^ (suc n))
    bound-sum = ≤Monotone+ (abs A) (inv2^ m ℚP.- inv2^ n) (abs B) (inv2^ (suc n)) IH dc-bound

    bound-simplify : (inv2^ m ℚP.- inv2^ n) ℚP.+ inv2^ (suc n)
                   ≡ inv2^ m ℚP.- inv2^ (suc n)
    bound-simplify = cong (λ x → (inv2^ m ℚP.- x) ℚP.+ inv2^ (suc n)) inv2^-double-at-n
                   ∙ minus-double-plus-half (inv2^ m) (inv2^ (suc n))

    -- Combine for suc n
    combined : abs (A ℚP.+ B) ℚO.≤ (inv2^ m ℚP.- inv2^ (suc n))
    combined = isTrans≤ (abs (A + B)) (abs A + abs B) _ step2
               (subst (λ x → (abs A + abs B) ℚO.≤ x) bound-simplify bound-sum)

    for-suc-n : abs (approx s (suc n) ℚP.- approx s m) ℚO.≤ (inv2^ m ℚP.- inv2^ (suc n))
    for-suc-n = subst (λ x → abs x ℚO.≤ _) (sym diff-decomp) combined

    -- Now use suc n = suc (m + k) = m + suc k to get the goal
    -- We have: suc n ≡ m + suc k via sym (+-suc m k)
    goal-path : (suc n ≡ m ℕ.+ suc k)
    goal-path = sym (ℕP.+-suc m k)
  in subst (λ x → abs (approx s x ℚP.- approx s m) ℚO.≤ (inv2^ m ℚP.- inv2^ x)) goal-path for-suc-n

-- Weaken tight bound to weak bound
tail-bound-step : (s : 𝟛ᴺ) (m k : ℕ)
  → abs (approx s (m ℕ.+ k) ℚP.- approx s m) ℚO.≤ inv2^ m
  → abs (approx s (m ℕ.+ suc k) ℚP.- approx s m) ℚO.≤ inv2^ m
tail-bound-step s m k _ = ≤-minus-weaken m (suc k) (abs (approx s (m ℕ.+ suc k) ℚP.- approx s m)) (tail-bound-tight s m (suc k))

-- Main tail bound: for m ≤ n, |approx s n - approx s m| ≤ 1/2^{m+1}
-- Proof by induction on k where n = m + k (using ≤-k+ to decompose m ≤ n)
-- Note: ≤-k+ gives (k , k + m ≡ n), so we use +-comm to get m + k ≡ n
tail-bound : (s : 𝟛ᴺ) (m n : ℕ) → m ≤ℕ n
  → abs (approx s n ℚP.- approx s m) ℚO.≤ inv2^ m
tail-bound s m n m≤n with ℕO.≤-k+ m≤n  -- gives (k , k + m ≡ n)
... | k , p = subst (λ x → abs (approx s x ℚP.- approx s m) ℚO.≤ inv2^ m) 
                    (ℕP.+-comm m k ∙ p) (go s m k)
  where
    -- Prove by induction on k
    go : (s : 𝟛ᴺ) (m k : ℕ) → abs (approx s (m ℕ.+ k) ℚP.- approx s m) ℚO.≤ inv2^ m
    go s m zero = subst (λ x → abs (approx s x ℚP.- approx s m) ℚO.≤ inv2^ m)
                        (sym (ℕP.+-zero m)) (tail-bound-base s m)
    go s m (suc k) = tail-bound-step s m k (go s m k)

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
