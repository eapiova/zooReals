{-# OPTIONS --cubical #-}

------------------------------------------------------------------------
-- Midpoint Algebra Signature for Signed-Digit Reals
------------------------------------------------------------------------
--
-- Following Escardó & Simpson, "A universal characterization of the
-- closed Euclidean interval" (2001/2014):
--
-- A midpoint algebra is a set with a binary operation _⊕_ satisfying:
--   • idempotency:  x ⊕ x ≡ x
--   • commutativity: x ⊕ y ≡ y ⊕ x
--   • mediality (transpositionality):
--       (a ⊕ b) ⊕ (c ⊕ d) ≡ (a ⊕ c) ⊕ (b ⊕ d)
--
-- A pointed midpoint algebra additionally has generators bot, top
-- (representing -1, +1), with mid = bot ⊕ top (representing 0).
--
-- The signed-digit structure arises because cons d x = digitPoint d ⊕ x.
--
-- POSTULATES: None. This module is pure algebra.

module Reals.SignedDigit.Midpoint.Algebra where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function using (_∘_)

open import Cubical.HITs.PropositionalTruncation using (∥_∥₁)

open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Sigma

open import Reals.SignedDigit.Core using (Digit; -1d; 0d; +1d)

------------------------------------------------------------------------
-- Midpoint Algebra
------------------------------------------------------------------------

record MidpointAlg : Type₁ where
  field
    Carrier : Type₀
    isSetCarrier : isSet Carrier
    _⊕_ : Carrier → Carrier → Carrier
    idem   : ∀ x → x ⊕ x ≡ x
    comm   : ∀ x y → x ⊕ y ≡ y ⊕ x
    medial : ∀ a b c d → (a ⊕ b) ⊕ (c ⊕ d) ≡ (a ⊕ c) ⊕ (b ⊕ d)

------------------------------------------------------------------------
-- Cancellative Midpoint Algebra
------------------------------------------------------------------------

record CancelMidpointAlg : Type₁ where
  field
    midpointAlg : MidpointAlg
  open MidpointAlg midpointAlg public
  field
    cancel : ∀ a b c → a ⊕ c ≡ b ⊕ c → a ≡ b

------------------------------------------------------------------------
-- Iterative Midpoint Algebra
------------------------------------------------------------------------
-- The iteration operator M assigns a "limit" to every sequence.
-- Unfolding says M a = a(0) ⊕ M(a ∘ suc), i.e., the limit of
-- iterated midpoints.

record IterMidpointAlg : Type₁ where
  field
    cancelMidpointAlg : CancelMidpointAlg
  open CancelMidpointAlg cancelMidpointAlg public
  field
    M    : (ℕ → Carrier) → Carrier
    M-eq : ∀ a → M a ≡ (a 0) ⊕ M (a ∘ suc)

------------------------------------------------------------------------
-- Pointed Midpoint Algebra
------------------------------------------------------------------------
-- A midpoint algebra with distinguished generators bot and top
-- (representing -1 and +1). The derived element mid = bot ⊕ top
-- represents 0.

record PointedMidpointAlg : Type₁ where
  field
    midpointAlg : MidpointAlg
  open MidpointAlg midpointAlg public
  field
    bot top : Carrier

  mid : Carrier
  mid = bot ⊕ top

  digitPoint : Digit → Carrier
  digitPoint -1d = bot
  digitPoint  0d = mid
  digitPoint +1d = top

------------------------------------------------------------------------
-- Helper: compute digitPoint from components
------------------------------------------------------------------------

mkDigitPoint : {A : Type₀} → (A → A → A) → A → A → Digit → A
mkDigitPoint _⊕_ bot top -1d = bot
mkDigitPoint _⊕_ bot top  0d = bot ⊕ top
mkDigitPoint _⊕_ bot top +1d = top

------------------------------------------------------------------------
-- Pointed Iterative Midpoint Algebra
------------------------------------------------------------------------
-- Extends PointedMidpointAlg with cancellation, iteration, and a
-- generation axiom (every element decomposes as digitPoint d ⊕ x).
--
-- Note: gen is NOT derivable from M alone. M says "every sequence
-- converges" but not "every element is a convergent digit-sequence."

record PointedIterMidpointAlg : Type₁ where
  field
    iterMidpointAlg : IterMidpointAlg
  open IterMidpointAlg iterMidpointAlg public
  field
    bot top : Carrier
    gen : ∀ y → ∥ Σ[ d ∈ Digit ] Σ[ x ∈ Carrier ]
                   (y ≡ mkDigitPoint _⊕_ bot top d ⊕ x) ∥₁

  mid : Carrier
  mid = bot ⊕ top

  digitPoint : Digit → Carrier
  digitPoint = mkDigitPoint _⊕_ bot top

------------------------------------------------------------------------
-- Midpoint Algebra Morphisms
------------------------------------------------------------------------

record MidpointHom (A B : MidpointAlg) : Type₀ where
  private
    module A = MidpointAlg A
    module B = MidpointAlg B

  field
    map  : A.Carrier → B.Carrier
    map-⊕ : ∀ x y → map (x A.⊕ y) ≡ map x B.⊕ map y

------------------------------------------------------------------------
-- Equality of morphisms
------------------------------------------------------------------------
-- Two MidpointHoms are equal iff their underlying maps are pointwise
-- equal. The map-⊕ field is an equality in a set, hence a proposition.

MidpointHom-path : {A B : MidpointAlg} (f g : MidpointHom A B)
                 → (∀ a → MidpointHom.map f a ≡ MidpointHom.map g a)
                 → f ≡ g
MidpointHom.map (MidpointHom-path f g h i) a = h a i
MidpointHom.map-⊕ (MidpointHom-path {A = A} {B = B} f g h i) x y =
  isProp→PathP (λ i → MidpointAlg.isSetCarrier B
    (h (MidpointAlg._⊕_ A x y) i) (MidpointAlg._⊕_ B (h x i) (h y i)))
    (MidpointHom.map-⊕ f x y) (MidpointHom.map-⊕ g x y) i

------------------------------------------------------------------------
-- Identity and composition
------------------------------------------------------------------------

MidpointHom-id : (A : MidpointAlg) → MidpointHom A A
MidpointHom.map (MidpointHom-id A) x = x
MidpointHom.map-⊕ (MidpointHom-id A) x y = refl

MidpointHom-comp : {A B C : MidpointAlg} → MidpointHom A B → MidpointHom B C → MidpointHom A C
MidpointHom.map (MidpointHom-comp f g) x = MidpointHom.map g (MidpointHom.map f x)
MidpointHom.map-⊕ (MidpointHom-comp f g) x y =
  cong (MidpointHom.map g) (MidpointHom.map-⊕ f x y) ∙ MidpointHom.map-⊕ g _ _

------------------------------------------------------------------------
-- Pointed Midpoint Algebra Morphisms
------------------------------------------------------------------------

record PointedMidpointHom (A B : PointedMidpointAlg) : Type₀ where
  private
    module A = PointedMidpointAlg A
    module B = PointedMidpointAlg B

  field
    hom : MidpointHom A.midpointAlg B.midpointAlg
  open MidpointHom hom public
  field
    map-bot : map A.bot ≡ B.bot
    map-top : map A.top ≡ B.top

  -- Derived: map preserves mid
  map-mid : map A.mid ≡ B.mid
  map-mid = map-⊕ A.bot A.top ∙ cong₂ B._⊕_ map-bot map-top

  -- Derived: map preserves digitPoint
  map-digitPoint : ∀ d → map (A.digitPoint d) ≡ B.digitPoint d
  map-digitPoint -1d = map-bot
  map-digitPoint  0d = map-mid
  map-digitPoint +1d = map-top
