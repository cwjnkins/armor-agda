{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509
import      Aeres.Data.X509.Properties.Time as Timeprops
open import Aeres.Prelude
open import Data.Nat.Properties
  hiding (_≟_)

module Aeres.Data.X509.Properties.ValidityFields where

open Base256
open import Aeres.Grammar.Definitions Dig

@0 iso : Iso (&ₚ Generic.Time Generic.Time) X509.ValidityFields
proj₁ (proj₁ iso) (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = X509.mkValidityFields fstₚ₁ sndₚ₁ bs≡
proj₂ (proj₁ iso) (X509.mkValidityFields start end bs≡) = mk&ₚ start end bs≡
proj₁ (proj₂ iso) (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = refl
proj₂ (proj₂ iso) (X509.mkValidityFields start end bs≡) = refl

@0 equivalent : _
equivalent = proj₁ iso

@0 nonnesting : NonNesting X509.ValidityFields
nonnesting x x₁ x₂ = foo
  where
  v2& : ∀ {bs} → X509.ValidityFields bs → (&ₚ Generic.Time Generic.Time) bs
  v2& (X509.mkValidityFields start end bs≡) = mk&ₚ start end bs≡
  foo = NonNesting&ₚ Timeprops.nonnesting Timeprops.nonnesting x (v2& x₁) (v2& x₂)

@0 unambiguous : Unambiguous X509.ValidityFields
unambiguous =
  isoUnambiguous iso
    (unambiguous&ₚ Timeprops.unambiguous Timeprops.nonnesting
      Timeprops.unambiguous)
