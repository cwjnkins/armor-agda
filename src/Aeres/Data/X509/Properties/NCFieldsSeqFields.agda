{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509
import      Aeres.Data.X509.Properties.GeneralSubtreeFields as GeneralSubtreeFieldsProps
open import Aeres.Data.X690-DER
open import Aeres.Prelude

module Aeres.Data.X509.Properties.NCFieldsSeqFields where

open Base256
open import Aeres.Grammar.Definitions UInt8
open import Aeres.Grammar.Properties  UInt8

equivalent : Equivalent (&ₚ (Option X509.PermittedSubtrees) (Option X509.ExcludedSubtrees)) X509.NCFieldsSeqFields
proj₁ equivalent (mk&ₚ fstₚ₁ sndₚ₁ refl) = X509.mkNCFieldsSeqFields fstₚ₁ sndₚ₁ refl
proj₂ equivalent (X509.mkNCFieldsSeqFields permt excld refl) = mk&ₚ permt excld refl


iso : Iso (&ₚ (Option X509.PermittedSubtrees) (Option X509.ExcludedSubtrees)) X509.NCFieldsSeqFields
proj₁ iso = equivalent
proj₁ (proj₂ iso) (mk&ₚ fstₚ₁ sndₚ₁ refl) = refl
proj₂ (proj₂ iso) (X509.mkNCFieldsSeqFields permt excld refl) = refl

@0 unambiguous : Unambiguous X509.NCFieldsSeqFields
unambiguous =
  isoUnambiguous iso
    (Unambiguous.option₂&₁
      (TLV.unambiguous (TLV.unambiguous (SequenceOf.Bounded.unambiguous (TLV.unambiguous GeneralSubtreeFieldsProps.unambiguous) TLV.nonempty TLV.nonnesting))) TLV.nonnesting TLV.nonempty
      (TLV.unambiguous (TLV.unambiguous (SequenceOf.Bounded.unambiguous (TLV.unambiguous GeneralSubtreeFieldsProps.unambiguous) TLV.nonempty TLV.nonnesting))) TLV.nonempty (TLV.noconfusion λ ()))
