{-# OPTIONS --cubical --guardedness #-}

------------------------------------------------------------------------
-- ℝ[-1,1] as a Pointed Midpoint Algebra; ι as a Homomorphism
------------------------------------------------------------------------
--
-- We show that the bounded subtype ℝ[-1,1] = Σ ℝ (λ x → -1 ≤ x × x ≤ 1)
-- carries a PointedMidpointAlg structure, and that the embedding
-- ι : 𝕀sd → ℝ lifts to a PointedMidpointHom ι↑ : 𝕀sd → ℝ[-1,1].
--
-- POSTULATES:
--   -1≤ᵣ+1      : rat(-1) ≤ᵣ rat(1) (provable: ≤ℚ→≤ᵣ + ℚ decision)
--   /2ᵣ-bounds  : /2ᵣ preserves [-1,1] (provable: ≤ᵣMonotone+ᵣ +
--                  Lipschitz monotonicity of /2ᵣ)
--   ι-bounded   : image of ι lies in [-1,1] (provable: partial sum
--                  bounds on stream→ℝ)
-- None require AC_ω.

module Reals.SignedDigit.Midpoint.RealStructure where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (isSetΣ; isProp×)

open import Cubical.Data.Sigma

open import Cubical.HITs.CauchyReals.Base using (ℝ; rat)
open import Cubical.HITs.CauchyReals.Closeness using (isSetℝ)
open import Cubical.HITs.CauchyReals.Order
  using (_+ᵣ_; _≤ᵣ_; isProp≤ᵣ; ≤ᵣ-refl)
open import Cubical.HITs.CauchyReals.Multiplication using (/2ᵣ)

open import Reals.SignedDigit.Core using (Digit; -1d; 0d; +1d)
open import Reals.SignedDigit.Bounded
  using ( 𝕀sd; ι; digitToℚ )
open import Reals.SignedDigit.Midpoint.Algebra
open import Reals.SignedDigit.Midpoint.Structure
  using ( 𝕀sd-MidAlg; _⊕𝕀_; ι-⊕; ι-bot; ι-top; bot𝕀; top𝕀
        ; /2ᵣ-x+x; /2ᵣ-+ᵣComm; medial-ℝ-lemma )

------------------------------------------------------------------------
-- ℝ[-1,1]: the bounded subtype
------------------------------------------------------------------------
-- Defined locally (same type as Safe/Bounded.ℝ[-1,1]) to avoid
-- the heavy Safe/Bounded import.

-1ℝ : ℝ
-1ℝ = rat (digitToℚ -1d)

+1ℝ : ℝ
+1ℝ = rat (digitToℚ +1d)

ℝ[-1,1] : Type₀
ℝ[-1,1] = Σ ℝ (λ x → (-1ℝ ≤ᵣ x) × (x ≤ᵣ +1ℝ))

isSetℝ[-1,1] : isSet ℝ[-1,1]
isSetℝ[-1,1] = isSetΣ isSetℝ
  (λ _ → isProp→isSet (isProp× (isProp≤ᵣ _ _) (isProp≤ᵣ _ _)))

-- Equality in ℝ[-1,1] reduces to equality of underlying ℝ values
ℝ[-1,1]-≡ : {a b : ℝ[-1,1]} → fst a ≡ fst b → a ≡ b
ℝ[-1,1]-≡ = Σ≡Prop (λ _ → isProp× (isProp≤ᵣ _ _) (isProp≤ᵣ _ _))

------------------------------------------------------------------------
-- Postulates: ℝ arithmetic for bounded interval
------------------------------------------------------------------------
-- All provable from ≤ᵣMonotone+ᵣ, Lipschitz /2ᵣ, and partial sums.
-- None require AC_ω.

postulate
  -- rat(-1) ≤ᵣ rat(1) in ℝ
  -- Proof: ≤ℚ→≤ᵣ applied to the ℚ decision procedure
  -1≤ᵣ+1 : -1ℝ ≤ᵣ +1ℝ

  -- /2ᵣ preserves [-1,1] bounds
  -- Proof: ≤ᵣMonotone+ᵣ gives (-1)+(-1) ≤ x+y ≤ 1+1,
  -- then /2ᵣ monotonicity (Lipschitz [1/2]) gives -1 ≤ /2ᵣ(x+y) ≤ 1
  /2ᵣ-bounds : ∀ x y
    → -1ℝ ≤ᵣ x → x ≤ᵣ +1ℝ
    → -1ℝ ≤ᵣ y → y ≤ᵣ +1ℝ
    → (-1ℝ ≤ᵣ /2ᵣ (x +ᵣ y)) × (/2ᵣ (x +ᵣ y) ≤ᵣ +1ℝ)

  -- ι maps into [-1,1]
  -- Proof: partial sums of stream→ℝ are bounded geometric series
  ι-bounded : ∀ (x : 𝕀sd) → (-1ℝ ≤ᵣ ι x) × (ι x ≤ᵣ +1ℝ)

------------------------------------------------------------------------
-- Midpoint operation on ℝ[-1,1]
------------------------------------------------------------------------

_⊕ℝ_ : ℝ[-1,1] → ℝ[-1,1] → ℝ[-1,1]
(x , lx , ux) ⊕ℝ (y , ly , uy) =
  /2ᵣ (x +ᵣ y) , /2ᵣ-bounds x y lx ux ly uy

------------------------------------------------------------------------
-- Midpoint axioms (via ℝ[-1,1]-≡ + ℝ arithmetic helpers)
------------------------------------------------------------------------

idem-ℝ : ∀ a → a ⊕ℝ a ≡ a
idem-ℝ (x , _) = ℝ[-1,1]-≡ (/2ᵣ-x+x x)

comm-ℝ : ∀ a b → a ⊕ℝ b ≡ b ⊕ℝ a
comm-ℝ (x , _) (y , _) = ℝ[-1,1]-≡ (/2ᵣ-+ᵣComm x y)

medial-ℝ : ∀ a b c d →
  (a ⊕ℝ b) ⊕ℝ (c ⊕ℝ d) ≡ (a ⊕ℝ c) ⊕ℝ (b ⊕ℝ d)
medial-ℝ (a , _) (b , _) (c , _) (d , _) =
  ℝ[-1,1]-≡ (medial-ℝ-lemma a b c d)

------------------------------------------------------------------------
-- Generators
------------------------------------------------------------------------

botℝ : ℝ[-1,1]
botℝ = -1ℝ , ≤ᵣ-refl -1ℝ , -1≤ᵣ+1

topℝ : ℝ[-1,1]
topℝ = +1ℝ , -1≤ᵣ+1 , ≤ᵣ-refl +1ℝ

------------------------------------------------------------------------
-- ℝ[-1,1] as a PointedMidpointAlg
------------------------------------------------------------------------

ℝ[-1,1]-MidAlg : PointedMidpointAlg
PointedMidpointAlg.midpointAlg ℝ[-1,1]-MidAlg = record
  { Carrier = ℝ[-1,1]
  ; isSetCarrier = isSetℝ[-1,1]
  ; _⊕_ = _⊕ℝ_
  ; idem = idem-ℝ
  ; comm = comm-ℝ
  ; medial = medial-ℝ
  }
PointedMidpointAlg.bot ℝ[-1,1]-MidAlg = botℝ
PointedMidpointAlg.top ℝ[-1,1]-MidAlg = topℝ

------------------------------------------------------------------------
-- Lift ι to ℝ[-1,1]
------------------------------------------------------------------------

ι↑ : 𝕀sd → ℝ[-1,1]
ι↑ x = ι x , ι-bounded x

------------------------------------------------------------------------
-- ι↑ is a PointedMidpointHom
------------------------------------------------------------------------

-- ι↑ preserves midpoint
ι↑-⊕ : ∀ x y → ι↑ (x ⊕𝕀 y) ≡ ι↑ x ⊕ℝ ι↑ y
ι↑-⊕ x y = ℝ[-1,1]-≡ (ι-⊕ x y)

-- ι↑ preserves generators
ι↑-bot : ι↑ bot𝕀 ≡ botℝ
ι↑-bot = ℝ[-1,1]-≡ ι-bot

ι↑-top : ι↑ top𝕀 ≡ topℝ
ι↑-top = ℝ[-1,1]-≡ ι-top

-- Package as a PointedMidpointHom
ι↑-Hom : PointedMidpointHom 𝕀sd-MidAlg ℝ[-1,1]-MidAlg
PointedMidpointHom.hom ι↑-Hom = record
  { map = ι↑
  ; map-⊕ = ι↑-⊕
  }
PointedMidpointHom.map-bot ι↑-Hom = ι↑-bot
PointedMidpointHom.map-top ι↑-Hom = ι↑-top
