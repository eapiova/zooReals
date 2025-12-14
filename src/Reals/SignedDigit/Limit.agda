{-# OPTIONS --cubical --guardedness #-}

------------------------------------------------------------------------
-- Limit Operation for Signed-Digit Streams
------------------------------------------------------------------------
--
-- This module implements the `lim` operation for signed-digit streams,
-- which allows defining a stream by a sequence of approximations that
-- converge effectively.
--
-- STATUS: Experimental/WIP using FIXMEs for arithmetic details.
--
------------------------------------------------------------------------

module Reals.SignedDigit.Limit where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_; _·_ to _*ℕ_)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Int
open import Cubical.Data.Rationals.Fast as ℚ
open import Cubical.Data.Rationals.Fast.Order as ℚO
open import Cubical.Data.Rationals.Fast.Properties as ℚP
open import Cubical.Relation.Nullary

open import Cubical.Codata.Stream

open import Reals.SignedDigit.Base
open import Reals.SignedDigit.Equivalence
open import Reals.SignedDigit.Embedding using (ι)
open import Reals.HoTT.Base

-- Local addition for Q+
infixl 6 _+₊_
_+₊_ : ℚ₊ → ℚ₊ → ℚ₊
(q , qp) +₊ (r , rp) = (q ℚP.+ r) , ?

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

-- Coherence helper: |2x - 2y| = 2|x - y|
postulate-abs-mult : (a b : ℚ.ℚ) → ℚP.abs (a ℚP.· b) ≡ ℚP.abs a ℚP.· ℚP.abs b
postulate-abs-mult a b = ?

abs-dist-scale : (x y : ℚ.ℚ) → ℚP.abs ((2Q ℚP.· x) ℚP.- (2Q ℚP.· y)) ≡ 2Q ℚP.· ℚP.abs (x ℚP.- y)
abs-dist-scale x y = ?

{-# TERMINATING #-}
limA : (f : ℚ₊ → 𝟛ᴺ) → (∀ δ ε → stream→ℝ (f δ) ∼[ δ +₊ ε ] stream→ℝ (f ε)) → 𝟛ᴺ
limA streams coh = record { head = d ; tail = limA nextStreams nextCoh }
  where
    -- Step 1: Pick fixed epsilon ε = 1/16
    ε = 1/16ℚ , ? -- Need Pos check

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
    -- f' δ = rational→stream (2 * approx(f (δ/4)) - d)
    nextStreams : ℚ₊ → 𝟛ᴺ
    nextStreams δ = rational→stream ((2Q ℚP.· q_δ) ℚP.- digitToℚ d)
      where 
        delta4 : ℚ₊
        delta4 = δ -- FIXME: division by 4
        
        q_δ : ℚ.ℚ
        q_δ = approx (streams delta4) 100n -- FIXME precision

    nextCoh : ∀ δ γ → stream→ℝ (nextStreams δ) ∼[ δ +₊ γ ] stream→ℝ (nextStreams γ)
    nextCoh δ γ = ? -- Use rat-rat-fromAbs logic
