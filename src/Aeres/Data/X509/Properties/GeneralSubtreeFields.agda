{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509
import      Aeres.Data.X509.Properties.GeneralName as GeneralNameProps
import      Aeres.Data.X509.Properties.Primitives as PrimProps
open import Aeres.Data.X690-DER
open import Aeres.Prelude

module Aeres.Data.X509.Properties.GeneralSubtreeFields where

open Base256
open import Aeres.Grammar.Definitions Dig
open import Aeres.Grammar.Properties  Dig

equivalent : Equivalent (&ₚ X509.GeneralName (&ₚ (Option X509.MinBaseDistance) (Option X509.MaxBaseDistance))) X509.GeneralSubtreeFields
proj₁ equivalent (mk&ₚ fstₚ₁ (mk&ₚ fstₚ₂ sndₚ₁ refl) refl) = X509.mkGeneralSubtreeFields fstₚ₁ fstₚ₂ sndₚ₁ refl
proj₂ equivalent (X509.mkGeneralSubtreeFields base minimum maximum refl) = (mk&ₚ base (mk&ₚ minimum maximum refl) refl)

iso : Iso (&ₚ X509.GeneralName (&ₚ (Option X509.MinBaseDistance) (Option X509.MaxBaseDistance))) X509.GeneralSubtreeFields
proj₁ iso = equivalent
proj₁ (proj₂ iso) (mk&ₚ fstₚ₁ (mk&ₚ fstₚ₂ sndₚ₁ refl) refl) = refl
proj₂ (proj₂ iso) (X509.mkGeneralSubtreeFields base minimum maximum refl) = refl

@0 unambiguous : Unambiguous X509.GeneralSubtreeFields
unambiguous =
  isoUnambiguous iso
    (unambiguous&ₚ GeneralNameProps.unambiguous GeneralNameProps.nonnesting
      (Unambiguous.option₂&₁
        (TLV.unambiguous  λ {xs} → PrimProps.IntegerValue.unambiguous {xs})  TLV.nonnesting TLV.nonempty
        (TLV.unambiguous  λ {xs} → PrimProps.IntegerValue.unambiguous {xs})  TLV.nonempty (TLV.noconfusion λ ())))
