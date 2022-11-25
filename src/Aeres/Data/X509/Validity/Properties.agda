{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.Validity.TCB
open import Aeres.Data.X690-DER.Time
import      Aeres.Grammar.Definitions
open import Aeres.Prelude
open import Data.Nat.Properties
  hiding (_≟_)

module Aeres.Data.X509.Validity.Properties where

open Aeres.Grammar.Definitions UInt8

iso : Iso (&ₚ Time Time) ValidityFields
proj₁ (proj₁ iso) (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = mkValidityFields fstₚ₁ sndₚ₁ bs≡
proj₂ (proj₁ iso) (mkValidityFields start end bs≡) = mk&ₚ start end bs≡
proj₁ (proj₂ iso) (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = refl
proj₂ (proj₂ iso) (mkValidityFields start end bs≡) = refl

equivalent : _
equivalent = proj₁ iso

@0 nonnesting : NonNesting ValidityFields
nonnesting x x₁ x₂ = foo
  where
  v2& : ∀ {bs} → ValidityFields bs → (&ₚ Time Time) bs
  v2& (mkValidityFields start end bs≡) = mk&ₚ start end bs≡
  foo = NonNesting&ₚ Time.nonnesting Time.nonnesting x (v2& x₁) (v2& x₂)

@0 unambiguous : Unambiguous ValidityFields
unambiguous =
  isoUnambiguous iso
    (unambiguous&ₚ Time.unambiguous Time.nonnesting
      Time.unambiguous)

instance
  EqValidity : Eq (Exists─ (List UInt8) ValidityFields)
  EqValidity = isoEq iso (eq&ₚ it it)

  eq≋ : Eq≋ ValidityFields
  eq≋ = Eq⇒Eq≋ it
