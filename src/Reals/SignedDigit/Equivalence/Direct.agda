{-# OPTIONS --cubical --guardedness #-}

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
-- NOTE: Arithmetic lemmas are in Equivalence.Arithmetic for faster compilation.
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

open import Cubical.HITs.CauchyReals.Base as ℝBase using (ℝ; rat; eqℝ; _∼[_]_; rat-rat-fromAbs; Recℝ; isProp∼)
open import Cubical.HITs.CauchyReals.Closeness using (triangle∼; sym∼)
open import Cubical.HITs.CauchyReals.Multiplication as ℝMul using (_·ᵣ_)

open import Reals.SignedDigit.Core
open import Reals.SignedDigit.Bounded using (𝕀sd; _≈sd_; isSet𝕀sd; stream→ℝ; rational→stream; clampℚ; clamp-lip; ι; -1ℚ; +1ℚ; 0ℚ)
open import Reals.SignedDigit.Representation using (ℝsd-raw; ℝsd; toℝ; toℝ-raw; pow2ℤ; isSetℝsd)
open import Reals.SignedDigit.Equivalence.Helpers using (ℝ∈OpenUnit; val; choose-k; 1ℚ₊)
open import Reals.SignedDigit.Equivalence.RoundTrip using (round-trip-clamped)
open import Reals.SignedDigit.Limit using (limA-𝕀sd; limA-𝕀sd-close)
open import Reals.SignedDigit.Equivalence.Arithmetic
  using (_+₊_; /2₊+/2₊≡ε₊)
open import Reals.SignedDigit.Equivalence.Coherence
  using (rat-rat-B-proof; rat-lim-B-proof; lim-rat-B-proof; lim-lim-B-proof)

-- Note: ℚ₊ addition alias (_+₊_) imported from Arithmetic

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

-- Convert coherence from modified B (∼[2ε]) to standard (∼[ε])
-- Given: ∀ ε → ι a ∼[ε +₊ ε] ι a'
-- Derive: ∀ ε → ι a ∼[ε] ι a' (by using ε/2)
B→std-close : (a a' : 𝕀sd) → (∀ ε → 𝕀sd-B a a' ε) → (∀ ε → ι a ∼[ ε ] ι a')
B→std-close a a' allClose ε = subst (λ x → ι a ∼[ x ] ι a') (/2₊+/2₊≡ε₊ ε) (allClose (/2₊ ε))

------------------------------------------------------------------------
-- Building the Recℝ structure for ℝ → 𝕀sd
------------------------------------------------------------------------

abstract
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

  -- Coherence proofs (imported from Coherence.agda for faster compilation)
  Recℝ.rat-rat-B ℝ→𝕀sd-Rec = rat-rat-B-proof
  Recℝ.rat-lim-B ℝ→𝕀sd-Rec = rat-lim-B-proof
  Recℝ.lim-rat-B ℝ→𝕀sd-Rec = lim-rat-B-proof
  Recℝ.lim-lim-B ℝ→𝕀sd-Rec = lim-lim-B-proof

  -- isPropB: closeness is a proposition
  -- Note: B a a' ε = ι a ∼[ε +₊ ε] ι a', so we use precision ε +₊ ε
  Recℝ.isPropB ℝ→𝕀sd-Rec a a' ε = isProp∼ (ι a) (ε +₊ ε) (ι a')

  ℝ→𝕀sd-direct : ℝ → 𝕀sd
  ℝ→𝕀sd-direct = Recℝ.go ℝ→𝕀sd-Rec

------------------------------------------------------------------------
-- The main embedding function
------------------------------------------------------------------------

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
