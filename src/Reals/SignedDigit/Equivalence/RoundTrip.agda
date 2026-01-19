{-# OPTIONS --cubical --guardedness --allow-unsolved-metas #-}

------------------------------------------------------------------------
-- Signed-Digit Equivalence: Round-Trip Proofs
------------------------------------------------------------------------
--
-- Proofs that rational→stream produces streams that converge back
-- to the original rational (when bounded) or its clamped value.
--
-- KEY EXPORTS:
--   round-trip-bounded  : Bounded rationals round-trip exactly
--   round-trip-clamped  : General rationals round-trip to their clamp
--   round-trip          : Alias for round-trip-clamped
--
------------------------------------------------------------------------

module Reals.SignedDigit.Equivalence.RoundTrip where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Data.Rationals.Fast as ℚ
open import Cubical.Data.Rationals.Fast.Properties as ℚP
open import Cubical.Data.Rationals.Fast.Order as ℚO
open import Cubical.Data.Rationals.Fast.Order.Properties as ℚOP using (/2₊; /3₊; ε/2+ε/2≡ε; ε/3+ε/3+ε/3≡ε; absComm-)

open import Cubical.HITs.CauchyReals.Base using (ℝ; rat; eqℝ; _∼[_]_; rat-rat-fromAbs)
open import Cubical.HITs.CauchyReals.Closeness using (triangle∼; sym∼)
open import Cubical.HITs.CauchyReals.Lipschitz using (𝕣-lim-self)

open import Reals.SignedDigit.Bounded using (stream→ℝ; rational→stream; clampℚ; -1ℚ; +1ℚ; rational→stream-clamp-eq; approxℚ₊; approxℚ₊-cauchy; approx-converges-ℚ₊)

------------------------------------------------------------------------
-- Round-trip proofs
------------------------------------------------------------------------

-- Bounded round-trip: if q is in [-1, 1], its stream converges to q
round-trip-bounded : (q : ℚ.ℚ) → -1ℚ ℚO.≤ q → q ℚO.≤ +1ℚ → stream→ℝ (rational→stream q) ≡ rat q
round-trip-bounded q lo hi = eqℝ (stream→ℝ s) (rat q) all-close
  where
    s = rational→stream q

    -- Strategy for all-close:
    -- 1. By 𝕣-lim-self: rat (approxℚ₊ s δ) ∼[ δ + ε' ] stream→ℝ s
    -- 2. By sym∼: stream→ℝ s ∼[ δ + ε' ] rat (approxℚ₊ s δ)
    -- 3. By approx-converges-ℚ₊: |q - approxℚ₊ s δ| < δ, so rat (approxℚ₊ s δ) ∼[δ] rat q
    -- 4. By triangle∼: stream→ℝ s ∼[ (δ + ε') + δ ] rat q
    --
    -- For the sum (δ + ε') + δ = ε, we set δ = ε' = ε/3:
    --   (ε/3 + ε/3) + ε/3 = ε

    all-close : (ε : ℚO.ℚ₊) → stream→ℝ s ∼[ ε ] rat q
    all-close ε =
      let
        δ = ℚOP./3₊ ε  -- δ = ε/3

        -- Stream representation: stream→ℝ s = lim (λ ε → rat (approxℚ₊ s ε)) (approxℚ₊-cauchy s)
        -- By 𝕣-lim-self: rat (approxℚ₊ s δ) ∼[ δ + δ ] stream→ℝ s
        lim-close : rat (approxℚ₊ s δ) ∼[ δ ℚO.ℚ₊+ δ ] stream→ℝ s
        lim-close = 𝕣-lim-self (λ ε' → rat (approxℚ₊ s ε')) (approxℚ₊-cauchy s) δ δ

        -- By sym∼: stream→ℝ s ∼[ δ + δ ] rat (approxℚ₊ s δ)
        stream-close-approx : stream→ℝ s ∼[ δ ℚO.ℚ₊+ δ ] rat (approxℚ₊ s δ)
        stream-close-approx = sym∼ _ _ _ lim-close

        -- By approx-converges-ℚ₊: |q - approxℚ₊ s δ| < δ
        approx-bound : ℚP.abs (q ℚP.- approxℚ₊ s δ) ℚO.< fst δ
        approx-bound = approx-converges-ℚ₊ q lo hi δ

        -- Convert to closeness: rat (approxℚ₊ s δ) ∼[δ] rat q
        -- Need |approxℚ₊ s δ - q| < δ, which is same as |q - approxℚ₊ s δ| < δ
        approx-bound' : ℚP.abs (approxℚ₊ s δ ℚP.- q) ℚO.< fst δ
        approx-bound' = subst (ℚO._< fst δ) (ℚOP.absComm- q (approxℚ₊ s δ)) approx-bound

        -- rat-rat-fromAbs takes |q - r| < ε and returns rat q ∼[ε] rat r
        approx-close-q : rat (approxℚ₊ s δ) ∼[ δ ] rat q
        approx-close-q = rat-rat-fromAbs (approxℚ₊ s δ) q δ approx-bound'

        -- Combine via triangle∼: stream→ℝ s ∼[ (δ + δ) + δ ] rat q
        -- With δ = ε/3: (ε/3 + ε/3) + ε/3 = ε

        -- ε/3+ε/3+ε/3≡ε gives: (fst ε · 1/3) + ((fst ε · 1/3) + (fst ε · 1/3)) ≡ fst ε
        -- i.e., a + (a + a) ≡ fst ε
        -- We need to show (δ + δ) + δ ≡ ε, i.e., (a + a) + a ≡ fst ε
        -- Use associativity: (a + a) + a = a + (a + a)
        a = fst δ  -- a = fst ε · 1/3

        -- Step 1: (a + a) + a ≡ a + (a + a) by associativity
        assoc : (a ℚ.+ a) ℚ.+ a ≡ a ℚ.+ (a ℚ.+ a)
        assoc = sym (ℚP.+Assoc a a a)

        -- Step 2: a + (a + a) ≡ fst ε by the lemma
        sum≡ε : a ℚ.+ (a ℚ.+ a) ≡ fst ε
        sum≡ε = ℚOP.ε/3+ε/3+ε/3≡ε (fst ε)

        δ+δ+δ≡ε : (δ ℚO.ℚ₊+ δ) ℚO.ℚ₊+ δ ≡ ε
        δ+δ+δ≡ε = ℚO.ℚ₊≡ (assoc ∙ sum≡ε)

      in subst (stream→ℝ s ∼[_] rat q) δ+δ+δ≡ε
           (triangle∼ stream-close-approx approx-close-q)

-- General round-trip: stream converges to clamp q
round-trip-clamped : (q : ℚ.ℚ) → stream→ℝ (rational→stream q) ≡ rat (clampℚ q)
round-trip-clamped q =
  cong stream→ℝ (rational→stream-clamp-eq q)
  ∙ round-trip-bounded (clampℚ q) -1≤clamp clamp≤1
  where
    -- clampℚ q = max -1 (min +1 q)
    -- For -1 ≤ max -1 (min +1 q), we use: a ≤ max a b for any a, b
    -- This follows from isTotal≤ a b giving either a ≤ b or b ≤ a
    -- If a ≤ b: max a b = b, and we need a ≤ b which we have
    -- If b ≤ a: max a b = a by maxComm, and we need a ≤ a (refl)
    -1≤clamp : -1ℚ ℚO.≤ clampℚ q
    -1≤clamp = PT.rec (ℚO.isProp≤ _ _) handle (ℚO.isTotal≤ -1ℚ (ℚP.min +1ℚ q))
      where
        -- We need to handle the cases for max
        handle : (-1ℚ ℚO.≤ ℚP.min +1ℚ q) ⊎ (ℚP.min +1ℚ q ℚO.≤ -1ℚ) → -1ℚ ℚO.≤ clampℚ q
        handle (inl neg1≤min) =
          -- max -1 (min +1 q) = min +1 q by ≤→max
          subst (-1ℚ ℚO.≤_) (sym (ℚO.≤→max -1ℚ (ℚP.min +1ℚ q) neg1≤min)) neg1≤min
        handle (inr min≤neg1) =
          -- max -1 (min +1 q) = -1 since min ≤ -1
          subst (-1ℚ ℚO.≤_) (sym (ℚP.maxComm -1ℚ (ℚP.min +1ℚ q) ∙ ℚO.≤→max (ℚP.min +1ℚ q) -1ℚ min≤neg1)) (ℚO.isRefl≤ -1ℚ)

    -- For clamp q ≤ +1, we need max -1 (min +1 q) ≤ +1
    -- min +1 q ≤ +1 (always), and -1 ≤ +1 (always)
    -- So max -1 (min +1 q) ≤ +1 by max-LUB pattern
    clamp≤1 : clampℚ q ℚO.≤ +1ℚ
    clamp≤1 = PT.rec (ℚO.isProp≤ _ _) handle (ℚO.isTotal≤ (ℚP.min +1ℚ q) -1ℚ)
        where
        -- min +1 q ≤ +1 always (min is less than left argument)
        min≤1 : ℚP.min +1ℚ q ℚO.≤ +1ℚ
        min≤1 = PT.rec (ℚO.isProp≤ _ _)
                  (λ { (inl 1≤q) → subst (ℚO._≤ +1ℚ) (sym (ℚO.≤→min +1ℚ q 1≤q)) (ℚO.isRefl≤ +1ℚ)
                     ; (inr q≤1) → subst (ℚO._≤ +1ℚ) (sym (ℚP.minComm +1ℚ q ∙ ℚO.≤→min q +1ℚ q≤1)) q≤1 })
                  (ℚO.isTotal≤ +1ℚ q)

        -- -1 ≤ +1: Construct directly using the ℤ≤ witness
        -- ℚO.≤ is defined via the underlying ℤ ordering
        -- -1 + 2 = +1, so we provide witness k = 2
        neg1≤1 : -1ℚ ℚO.≤ +1ℚ
        neg1≤1 = ℚO.inj (2 , refl)

        handle : (ℚP.min +1ℚ q ℚO.≤ -1ℚ) ⊎ (-1ℚ ℚO.≤ ℚP.min +1ℚ q) → clampℚ q ℚO.≤ +1ℚ
        handle (inl min≤neg1) =
          -- max -1 (min +1 q) = -1 since min ≤ -1
          subst (ℚO._≤ +1ℚ)
                (sym (ℚP.maxComm -1ℚ (ℚP.min +1ℚ q) ∙ ℚO.≤→max (ℚP.min +1ℚ q) -1ℚ min≤neg1))
                neg1≤1
        handle (inr neg1≤min) =
          -- max -1 (min +1 q) = min +1 q by ≤→max
          subst (ℚO._≤ +1ℚ) (sym (ℚO.≤→max -1ℚ (ℚP.min +1ℚ q) neg1≤min)) min≤1

-- OLD round-trip used in the file was: (q : ℚ) -> ... ≡ rat q
-- This is false for unbounded q. We replaced usages with round-trip-clamped logic.
round-trip : (q : ℚ.ℚ) → stream→ℝ (rational→stream q) ≡ rat (clampℚ q)
round-trip = round-trip-clamped
