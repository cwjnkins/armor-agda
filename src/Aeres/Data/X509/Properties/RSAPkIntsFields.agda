{-# OPTIONS --subtyping #-}

open import Aeres.Data.X509
import      Aeres.Grammar.Definitions
import      Aeres.Data.X509.Properties.BitstringValue as BitstringProps
import      Aeres.Data.X509.Properties.Primitives as PrimProps
open import Aeres.Data.X690-DER
open import Aeres.Prelude
open import Aeres.Binary
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Properties.RSAPkIntsFields where

open Base256
open Aeres.Grammar.Definitions Dig
open ≡-Reasoning


@0 nonnesting : NonNesting X509.RSAPkIntsFields
nonnesting x a₁ a₂ = foo
  where
  v2& :  ∀ {bs} → X509.RSAPkIntsFields bs → (&ₚ Int Int) bs
  v2& (X509.mkRSAPkIntsFields n e bs≡) = mk&ₚ n e bs≡
  foo = NonNesting&ₚ TLV.nonnesting TLV.nonnesting x (v2& a₁) (v2& a₂)

equivalent : Equivalent (&ₚ Int Int) X509.RSAPkIntsFields
proj₁ equivalent (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = X509.mkRSAPkIntsFields fstₚ₁ sndₚ₁ bs≡
proj₂ equivalent (X509.mkRSAPkIntsFields fstₚ₁ sndₚ₁ bs≡) = mk&ₚ fstₚ₁ sndₚ₁ bs≡

iso : Iso (&ₚ Int Int) X509.RSAPkIntsFields
proj₁ iso = equivalent
proj₁ (proj₂ iso) (Aeres.Grammar.Definitions.mk&ₚ fstₚ₁ sndₚ₁ bs≡) = refl
proj₂ (proj₂ iso) (X509.mkRSAPkIntsFields nval eval bs≡) = refl

@0 unambiguous : Unambiguous X509.RSAPkIntsFields
unambiguous = isoUnambiguous iso
                (unambiguous&ₚ
                (TLV.unambiguous λ {xs} → PrimProps.IntegerValue.unambiguous{xs})
                TLV.nonnesting
                (TLV.unambiguous λ {xs} → PrimProps.IntegerValue.unambiguous{xs}))
