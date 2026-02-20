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
--   /2ᵣ-bounds  : /2ᵣ preserves [-1,1] (provable: ≤ᵣMonotone+ᵣ +
--                  Lipschitz monotonicity of /2ᵣ)
--   (ι-bounded is provided in Reals.SignedDigit.Interval)
-- None require AC_ω.

module Reals.SignedDigit.Midpoint.RealStructure where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma using (_×_)
open import Cubical.HITs.CauchyReals.Base using (ℝ)
open import Cubical.HITs.CauchyReals.Order
  using (_+ᵣ_; +ᵣComm; _≤ᵣ_; ≤ᵣ-refl; decℚ≤ᵣ?)
open import Cubical.HITs.CauchyReals.Multiplication using (/2ᵣ)

open import Reals.SignedDigit.Interval public
  using ( -1ℝ
        ; +1ℝ
        ; ℝ[-1,1]
        ; isSetℝ[-1,1]
        ; ℝ[-1,1]-≡
        ; ι-bounded
        ; ι↑
        )
open import Reals.SignedDigit.Midpoint.Algebra
open import Reals.SignedDigit.Midpoint.Structure
  using ( 𝕀sd-MidAlg; _⊕𝕀_; ι-⊕; ι-bot; ι-top; bot𝕀; top𝕀
        ; /2ᵣ-x+x; medial-ℝ-lemma )

-- Postulates: ℝ arithmetic for bounded interval
------------------------------------------------------------------------
-- All provable from ≤ᵣMonotone+ᵣ, Lipschitz /2ᵣ, and partial sums.
-- None require AC_ω.

-- rat(-1) ≤ᵣ rat(1) in ℝ (via ℚ decision procedure)
-1≤ᵣ+1 : -1ℝ ≤ᵣ +1ℝ
-1≤ᵣ+1 = decℚ≤ᵣ?

postulate
  -- /2ᵣ preserves [-1,1] bounds
  -- Proof: ≤ᵣMonotone+ᵣ gives (-1)+(-1) ≤ x+y ≤ 1+1,
  -- then /2ᵣ monotonicity (Lipschitz [1/2]) gives -1 ≤ /2ᵣ(x+y) ≤ 1
  /2ᵣ-bounds : ∀ x y
    → -1ℝ ≤ᵣ x → x ≤ᵣ +1ℝ
    → -1ℝ ≤ᵣ y → y ≤ᵣ +1ℝ
    → (-1ℝ ≤ᵣ /2ᵣ (x +ᵣ y)) × (/2ᵣ (x +ᵣ y) ≤ᵣ +1ℝ)

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
comm-ℝ (x , _) (y , _) = ℝ[-1,1]-≡ (cong /2ᵣ (+ᵣComm x y))

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
