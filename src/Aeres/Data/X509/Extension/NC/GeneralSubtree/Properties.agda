{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.Extension.NC.GeneralSubtree.TCB
open import Aeres.Data.X509.GeneralName
open import Aeres.Data.X690-DER.Int
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Data.X690-DER.SequenceOf.TCB
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
import      Aeres.Grammar.Properties
open import Aeres.Prelude

module Aeres.Data.X509.Extension.NC.GeneralSubtree.Properties where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8
open Aeres.Grammar.Properties  UInt8

Rep = &ₚ GeneralName (&ₚ (Option MinBaseDistance) (Option MaxBaseDistance))

equivalent : Equivalent Rep GeneralSubtreeFields
proj₁ equivalent (mk&ₚ fstₚ₁ (mk&ₚ fstₚ₂ sndₚ₁ refl) refl) = mkGeneralSubtreeFields fstₚ₁ fstₚ₂ sndₚ₁ refl
proj₂ equivalent (mkGeneralSubtreeFields base minimum maximum refl) = (mk&ₚ base (mk&ₚ minimum maximum refl) refl)

iso : Iso Rep GeneralSubtreeFields
proj₁ iso = equivalent
proj₁ (proj₂ iso) (mk&ₚ fstₚ₁ (mk&ₚ fstₚ₂ sndₚ₁ refl) refl) = refl
proj₂ (proj₂ iso) (mkGeneralSubtreeFields base minimum maximum refl) = refl

@0 unambiguous : Unambiguous GeneralSubtreeFields
unambiguous =
  Iso.unambiguous iso
    (unambiguous&ₚ GeneralName.unambiguous GeneralName.nonnesting
      (Unambiguous.option₂&₁
        (TLV.unambiguous  λ {xs} → Int.unambiguous {xs})  TLV.nonnesting TLV.nonempty
        (TLV.unambiguous  λ {xs} → Int.unambiguous {xs})  TLV.nonempty (TLV.noconfusion λ ())))
