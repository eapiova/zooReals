{-# OPTIONS --cubical --guardedness #-}
module TempCheck where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Int.Fast as ℤ using (pos)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Rationals.Fast as ℚ using (ℚ ; [_/_])
open import Cubical.Data.Rationals.Fast.Order as ℚ using (ℚ₊)
open import Cubical.Data.Rationals.Fast.Order.Properties as ℚ
open import Cubical.HITs.CauchyReals.Base using (ℝ ; rat)
open import Cubical.HITs.CauchyReals.Lipschitz using (fromLipschitzGo; Lipschitz-ℚ→ℝ; Lipschitz-rat∘)
open import Cubical.HITs.CauchyReals.Multiplication using (/2ᵣ)
open import Cubical.Tactics.CommRingSolverFast.RationalsReflection
open import Cubical.Tactics.CommRingSolverFast.FastRationalsReflection

fromLipschitzGo-rat : ∀ {L lf q} → fst (fromLipschitzGo L lf) (rat q) ≡ fst lf q
fromLipschitzGo-rat = refl

/2ᵣ-rat : ∀ q → /2ᵣ (rat q) ≡ rat (q ℚ.· [ 1 / 2 ])
/2ᵣ-rat q = fromLipschitzGo-rat
  {L = ([ 1 / 2 ] , _)}
  {lf = (_ , Lipschitz-rat∘ ([ 1 / 2 ] , _) (ℚ._· [ 1 / 2 ])
    λ q r ε x →
      subst (ℚ._< ([ 1 / 2 ]) ℚ.· (fst ε))
       (sym (ℚ.pos·abs [ 1 / 2 ] (q ℚ.- r)
        (𝟚.toWitness {Q = ℚ.≤Dec 0 [ 1 / 2 ]} _ ))
        ∙ cong {x = ([ 1 / 2 ] ℚ.· (q ℚ.- r))}
               {y = ((q ℚ.· [ 1 / 2 ]) ℚ.- (r ℚ.· [ 1 / 2 ]))}
               ℚ.abs ℚ!!)
       (ℚ.<-o· (ℚ.abs (q ℚ.- r)) (fst ε) [ 1 / 2 ]
        ((𝟚.toWitness {Q = ℚ.<Dec 0 [ 1 / 2 ]} _ )) x))}
  {q = q}
