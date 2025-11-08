{-# OPTIONS --safe --cubical --guardedness #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

module Approx where

private
  variable
    ℓ : Level

module _
  (Q₊ Q R : Type)
  (ι₊ : Q₊ → Q)
  (ι : Q → R)
  (_+₊_ : Q₊ → Q₊ → Q₊ )
  (_/2 : Q₊ → Q₊)
  (/2+/2≡Id : ∀ ε → (ε /2) +₊ (ε /2) ≡ ε)
  (_∼[_]_ : R → Q₊ → R → Type)
  (refl∼ : ∀ {ε r} → r ∼[ ε ] r )
  (_∼_⟨_⟩ : ∀ {r s t ε δ η} → r ∼[ ε ] s → s ∼[ δ ] t → (ε +₊ δ ≡ η) → r ∼[ η ] t )
  (lim : (xs : Q₊ → R) → (xc : ∀ ε δ → xs ε ∼[ ε +₊ δ ] xs δ ) → R)
  (limIsLim : ∀ (xs : Q₊ → R) p (ε : Q₊) → xs ε ∼[ ε ] lim xs p)
  where

  record IsQApprox (x : R) : Type where
    field
      seq : Q₊ → Q
      seq∼ : ∀ ε → ι (seq ε) ∼[ ε ] x

  open IsQApprox

  module ∼Reasoning where

    infixl 5 ∼step
    _∼[_]⟨_⟩_≡Q₊[_] ∼step : ∀ (x : R)
                            → (ε : Q₊)
                            → {y : R}  → (x ∼[ ε ] y)
                            → {δ : Q₊} → {z : R} → (y ∼[ δ ] z)
                            → {η : Q₊} → (ε +₊ δ ≡ η)
                            → x ∼[ η ] z
    _∼[_]⟨_⟩_≡Q₊[_] x ε x∼ε∼y y∼δ∼z ε+δ≡η = x∼ε∼y ∼ y∼δ∼z ⟨ ε+δ≡η ⟩
    ∼step = _∼[_]⟨_⟩_≡Q₊[_]

    syntax ∼step x ε x∼ε∼y y∼δ∼z ε+δ≡η = by ε+δ≡η conclude x ∼[ ε ]⟨ x∼ε∼y ⟩ y∼δ∼z

    ∼∎syntax : ∀ (x y : R) → (ε : Q₊) → (x ∼[ ε ] y) → (x ∼[ ε ] y)
    ∼∎syntax x y ε x∼ε∼y = x∼ε∼y

    syntax ∼∎syntax x y ε x∼ε∼y = x ∼[ ε ]⟨ x∼ε∼y ⟩ y ∼∎

    _≡∼⟨_⟩_ : ∀ (x : R)
              → {y : R}  → (x ≡ y)
              → {δ : Q₊} → {z : R} → (y ∼[ δ ] z)
              → x ∼[ δ ] z
    _≡∼⟨_⟩_ x x≡y y∼δ∼z = subst (_∼[ _ ] _) (sym x≡y) y∼δ∼z

    _≡∼⟨⟩_ : ∀ (x : R)
              → {ε : Q₊} → {y : R} → (x ∼[ ε ] y)
              → x ∼[ ε ] y
    _≡∼⟨⟩_ x x∼ε∼y = x∼ε∼y

    _∼[_]⟨_⟩_∼≡_ : ∀ (x : R)
                   → (ε : Q₊)
                   → {y z : R}
                   → (x ∼[ ε ] y)
                   → (y ≡ z)
                   → x ∼[ ε ] z
    _∼[_]⟨_⟩_∼≡_ = λ x ε x∼ε∼y y≡z → subst (x ∼[ ε ]_) y≡z x∼ε∼y

  open ∼Reasoning

  IsQApprox-ι : ∀ {q} → IsQApprox (ι q)
  IsQApprox-ι {q} .seq  = λ _ → q
  IsQApprox-ι {q} .seq∼ = λ _ → refl∼

  isQApprox-lim : ∀ {r p} → (∀ ε → IsQApprox (r ε)) → IsQApprox (lim r p)
  isQApprox-lim {r} {p} r[_]approx .seq  ε = r[ ε /2 ]approx .seq (ε /2)
  isQApprox-lim {r} {p} r[_]approx .seq∼ ε = (r[ ε /2 ]approx .seq∼ (ε /2) :>
    ( ι (r[ ε /2 ]approx .seq (ε /2))  ∼[ ε /2 ]
         r (ε /2))                  )  ∼ limIsLim r p (ε /2) :>
    (    r (ε /2)                      ∼[ ε /2 ]
      lim r p)                         ⟨ /2+/2≡Id ε ⟩

  isQApprox-lim' : ∀ {r p} → (∀ ε → IsQApprox (r ε)) → IsQApprox (lim r p)
  isQApprox-lim' {r} {p} r[_]approx .seq  ε = r[ ε /2 ]approx .seq (ε /2)
  isQApprox-lim' {r} {p} r[_]approx .seq∼ ε =
    ι (r[ ε /2 ]approx .seq (ε /2)) ∼[ ε /2 ]⟨ r[ ε /2 ]approx .seq∼ (ε /2) ⟩
    r (ε /2)                        ∼[ ε /2 ]⟨ limIsLim r p (ε /2) ⟩
    lim r p                         ∼∎
    ≡Q₊[ /2+/2≡Id ε ]

  isQApprox-lim'' : ∀ {r p} → (∀ ε → IsQApprox (r ε)) → IsQApprox (lim r p)
  isQApprox-lim'' {r} {p} r[_]approx .seq  ε = r[ ε /2 ]approx .seq (ε /2)
  isQApprox-lim'' {r} {p} r[_]approx .seq∼ ε =
    by
      /2+/2≡Id ε :> (ε /2) +₊ (ε /2) ≡ ε
    conclude
      ι (r[ ε /2 ]approx .seq (ε /2)) ∼[ ε /2 ]⟨ r[ ε /2 ]approx .seq∼ (ε /2) ⟩
      r (ε /2)                        ∼[ ε /2 ]⟨ limIsLim r p (ε /2) ⟩
      lim r p                         ∼∎

  -- sends approximaple inputs to approximable outputs
  -- cf "functions that lift to locators" in A. Booij PhD Thesis
  QApproxLift : (R → R) → Type
  QApproxLift f = ∀ x → IsQApprox x → IsQApprox (f x)
