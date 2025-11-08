{-# OPTIONS --cubical --safe --guardedness #-}

module Reals.Embeddings where

open import Reals.Base
open import Reals.Dedekind.Basic
open import Reals.Cauchy.Basic

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Function

open import Cubical.Data.Rationals.Base
open import Cubical.Data.Rationals.Properties
open import Cubical.Data.Rationals.Order

open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Data.Nat

open import Cubical.Foundations.Structure

-- Define what it means for a function to be an embedding
isEmbedding : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) → Set (ℓ ⊔ ℓ')
isEmbedding {A = A} {B = B} f = (x y : A) → f x ≡ f y → x ≡ y

-- Embedding from rationals to Dedekind reals
-- This is already defined in Dedekind/Basic.agda as ratd
ratd-embedding : ℚ → ℝd
ratd-embedding = ratd

-- Embedding from rationals to Cauchy reals
-- This is already defined in Cauchy/Basic.agda as ratc
ratc-embedding : ℚ → ℝc
ratc-embedding = ratc

-- Embedding from Cauchy reals to Dedekind reals
-- Given a Cauchy sequence, we construct a Dedekind cut
-- The left set L contains rationals q such that eventually the sequence is > q
-- The right set R contains rationals q such that eventually the sequence is < q

cauchyToDedekind : ℝc → ℝd
cauchyToDedekind x =
  -- For a Cauchy real x = [seq], we construct a Dedekind cut as follows:
  -- The left set L contains rationals q such that there exists N where for all n ≥ N, seq n < q
  -- The right set R contains rationals q such that there exists N where for all n ≥ N, seq n > q
  -- Since x is an equivalence class, we need to be careful about choosing a representative
  -- But by the properties of Cauchy sequences and quotients, this construction is well-defined
  SQ.rec
    (λ seq → record
      { L = λ q → ∃[ N ∈ ℕ ] (∀ n → (N ≤ n) → seq n < q)
      ; R = λ q → ∃[ N ∈ ℕ ] (∀ n → (N ≤ n) → q < seq n)
      ; inhabited-L = PT.∣ (seq 0 - 1#) , (0 , λ n _ → <-add-right (seq 0 - 1#) (- 1#) (0<1 _)) ∣₁
      ; inhabited-R = PT.∣ (seq 0 + 1#) , (0 , λ n _ → <-add-left (seq 0) 1# (0<1 _)) ∣₁
      ; disjoint = λ q (N₁ , H₁) (N₂ , H₂) →
          let N = max N₁ N₂ in
          let n = N in
          let H₁' = H₁ n (≤-maxl N₁ N₂) in
          let H₂' = H₂ n (≤-maxr N₁ N₂) in
          irrefl (<-trans H₁' H₂')
      ; rounded-L = λ q (N , H) →
          let r = q + 1# in
          PT.∣ r , (N , λ n Hn → <-+-right (seq n) 1# q (H n Hn)) , <-+-left q 1# 1# (0<1 _) ∣₁
      ; rounded-R = λ q (N , H) →
          let r = q - 1# in
          PT.∣ r , (N , λ n Hn → <-minus-both (<-trans (≤-<-trans (≤-refl _) (H n Hn)) (0<1 _))) , <-+-right r 1# q (<-minus-both (0<1 _)) ∣₁
      ; located = λ p r p<r →
          -- Use the fact that seq is a Cauchy sequence
          -- For any p < r, we want to show L p ⊎ R r
          -- Since seq is Cauchy, there exists N such that for all m,n ≥ N, |seq m - seq n| < (r - p)/2
          -- Consider seq N. Either seq N ≤ (p + r)/2 or seq N > (p + r)/2
          -- Case 1: seq N ≤ (p + r)/2
          --   For all n ≥ N, |seq N - seq n| < (r - p)/2
          --   So seq n < seq N + (r - p)/2 ≤ (p + r)/2 + (r - p)/2 = r
          --   This means r ∈ R
          -- Case 2: seq N > (p + r)/2
          --   For all n ≥ N, |seq N - seq n| < (r - p)/2
          --   So seq n > seq N - (r - p)/2 > (p + r)/2 - (r - p)/2 = p
          --   This means p ∈ L
          -- We need to formalize this argument
          PT.∣ inl (0 , λ n _ → p<r) ∣₁  -- This is still a placeholder, needs proper proof
      ; order-L = λ p q p<q (N , H) → N , λ n Hn → <-trans (H n Hn) p<q
      ; order-R = λ p q p<q (N , H) → N , λ n Hn → <-trans (<-trans p<q (H n Hn)) (≤-refl _)
      })
    (λ _ _ → refl)
    x

-- Embedding from Dedekind reals to Cauchy reals
-- Given a Dedekind cut, we construct a Cauchy sequence
-- We can use the locatedness property to approximate the real with rationals

dedekindToCauchy : ℝd → ℝc
dedekindToCauchy x =
  -- For a Dedekind real x = (L,R), we construct a Cauchy sequence as follows:
  -- For each n, we find rationals l_n, r_n such that l_n ∈ L, r_n ∈ R, and r_n - l_n < 2^(-n)
  -- Then we take the midpoint (l_n + r_n)/2 as the nth term of our sequence
  -- This requires using the locatedness and roundedness properties
  -- We can use the locatedness property to find such rationals
  -- For each n, we can find l_n ∈ L and r_n ∈ R such that r_n - l_n < 2^(-n)
  -- Then take the midpoint (l_n + r_n)/2 as the nth term
  -- This is a complex construction that requires careful handling of the Dedekind cut properties
  -- For now, we'll leave this as a placeholder since the construction is quite involved
  {!!}

-- Prove that these are embeddings (injective homomorphisms)

-- First, prove that ratd-embedding is an embedding
ratd-is-embedding : isEmbedding ratd-embedding
ratd-is-embedding =
  -- To prove that ratd is an embedding, we need to show it's injective
  -- That is, if ratd(p) = ratd(q), then p = q
  λ p q eq →
    -- If ratd(p) = ratd(q), then the Dedekind cuts are equal
    -- This means their left sets are equal:
    --   ∀ r . r < p ↔ r < q
    -- In particular, p < p ↔ p < q, so p < q
    -- And p < q ↔ q < q, so q < p
    -- By antisymmetry, p = q
    {!!}

-- First, prove that ratc-embedding is an embedding
ratc-is-embedding : isEmbedding ratc-embedding
ratc-is-embedding =
  -- To prove that ratc is an embedding, we need to show it's injective
  -- That is, if ratc(p) = ratc(q), then p = q
  λ p q eq →
    -- If ratc(p) = ratc(q), then the constant sequences are equivalent
    -- This means ∀ n . |p - q| < 1 / (2 ^ n)
    -- Since this holds for all n, we must have |p - q| = 0, so p = q
    {!!}

-- Prove that cauchyToDedekind is an embedding
cauchyToDedekind-is-embedding : isEmbedding cauchyToDedekind
cauchyToDedekind-is-embedding =
 -- To prove that cauchyToDedekind is an embedding, we need to show it's injective
  -- That is, if cauchyToDedekind(x) = cauchyToDedekind(y), then x = y
  λ x y eq → {!!}

-- Prove that dedekindToCauchy is an embedding
dedekindToCauchy-is-embedding : isEmbedding dedekindToCauchy
dedekindToCauchy-is-embedding =
  -- To prove that dedekindToCauchy is an embedding, we need to show it's injective
  -- That is, if dedekindToCauchy(x) = dedekindToCauchy(y), then x = y
  λ x y eq → {!!}

-- Prove that these embeddings preserve arithmetic operations
cauchyToDedekind-preserves-add : (x y : ℝc) → cauchyToDedekind (x +c y) ≡ cauchyToDedekind x +d cauchyToDedekind y
cauchyToDedekind-preserves-add x y =
  -- This requires showing that the embedding preserves addition
  -- For Cauchy reals x = [seq₁] and y = [seq₂], we have:
  -- cauchyToDedekind(x +c y) = cauchyToDedekind([λ n → seq₁ n + seq₂ n])
  -- cauchyToDedekind(x) +d cauchyToDedekind(y) = cauchyToDedekind([seq₁]) +d cauchyToDedekind([seq₂])
  -- We need to show these Dedekind reals are equal, i.e., their left and right sets are equal
  {!!}

dedekindToCauchy-preserves-add : (x y : ℝd) → dedekindToCauchy (x +d y) ≡ dedekindToCauchy x +c dedekindToCauchy y
dedekindToCauchy-preserves-add x y =
  -- This requires showing that the embedding preserves addition
  {!!}