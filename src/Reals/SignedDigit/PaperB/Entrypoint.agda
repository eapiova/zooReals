{-# OPTIONS --cubical --guardedness #-}

------------------------------------------------------------------------
-- Paper B Entrypoint: HCIT Algebra Formulation + Quotient Model
------------------------------------------------------------------------
--
-- Stable reviewer-facing API for Paper B.
-- Naming for HCIT fields/lemmas is frozen here to avoid drift:
--   inc⁻¹, inc⁰, inc⁺¹, dec⁺¹, dec⁰, dec⁻¹,
--   carry, borrow, carry-compl, borrow-compl, sep-L, sep-R, gen.

module Reals.SignedDigit.PaperB.Entrypoint where

open import Cubical.Foundations.Prelude

open import Reals.SignedDigit.IncDec public
  using ( inc
        ; dec
        ; inc𝕀
        ; dec𝕀
        ; carry𝕀
        ; borrow𝕀
        ; inc-resp
        ; dec-resp
        ; carry-raw
        ; borrow-raw
        )

open import Reals.SignedDigit.HCIT.Algebra public
  using ( 𝕀-Alg
        ; 𝕀-Hom
        ; 𝕀-id
        ; 𝕀-comp
        ; 𝕀-Hom-path
        )

open import Reals.SignedDigit.HCIT.Structure public
  using ( cons𝕀
        ; inc⁻¹-𝕀
        ; inc⁰-𝕀
        ; inc⁺¹-𝕀
        ; dec⁺¹-𝕀
        ; dec⁰-𝕀
        ; dec⁻¹-𝕀
        ; carry-𝕀
        ; borrow-𝕀
        ; gen-𝕀
        ; carry-compl-𝕀
        ; borrow-compl-𝕀
        ; sep-L-𝕀
        ; sep-R-𝕀
        ; 𝕀sd-Alg
        )

open import Reals.SignedDigit.HCIT.Terminality public
  using ( ι-inj
        ; sem
        ; sem-cons
        ; sem-𝕀sd
        ; morph
        ; morph-is-hom
        ; morph-unique
        ; isTerminal-𝕀sd
        )

-- Frozen field naming surface for any 𝕀-algebra instance.
module StableAlg (A : 𝕀-Alg) where
  open 𝕀-Alg A public
    using ( cons
          ; inc
          ; dec
          ; inc⁻¹
          ; inc⁰
          ; inc⁺¹
          ; dec⁺¹
          ; dec⁰
          ; dec⁻¹
          ; carry
          ; borrow
          ; gen
          ; carry-compl
          ; borrow-compl
          ; sep-L
          ; sep-R
          )
