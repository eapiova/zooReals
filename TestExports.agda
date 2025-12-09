module TestExports where
open import Cubical.Foundations.Prelude
open import Cubical.Data.Int using (pos; negsuc)
open import Cubical.Data.NatPlusOne using (1+_)
open import Cubical.Data.Rationals.Base as ℚB using (ℚ; [_/_]; isSetℚ)
open import Cubical.Data.Rationals.Properties
open import Cubical.HITs.SetQuotients as SQ

1ℚ = [ pos 1 / 1+ 0 ]
-1ℚ = [ negsuc 0 / 1+ 0 ]

-- Try using the eliminator
·NegOneL : (x : ℚ) → -1ℚ · x ≡ - x
·NegOneL = SQ.elimProp (λ _ → isSetℚ _ _) go
  where
    go : (a : _ ) → -1ℚ · SQ.[ a ] ≡ - SQ.[ a ]
    go a = refl
