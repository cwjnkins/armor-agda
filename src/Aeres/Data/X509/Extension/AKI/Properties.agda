{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.Extension.AKI.TCB
open import Aeres.Data.X509.GeneralName
open import Aeres.Data.X690-DER.Int
open import Aeres.Data.X690-DER.OctetString
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
import      Aeres.Grammar.Properties

open import Aeres.Prelude

module Aeres.Data.X509.Extension.AKI.Properties where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8
open Aeres.Grammar.Properties  UInt8

Rep = &ₚ (Option AKIKeyId) (&ₚ (Option AKIAuthCertIssuer) (Option AKIAuthCertSN))

equivalent : Equivalent Rep AKIFieldsSeqFields
proj₁ equivalent (mk&ₚ v₁ (mk&ₚ v₂ v₃ refl) refl) = mkAKIFieldsSeqFields v₁ v₂ v₃ refl
proj₂ equivalent (mkAKIFieldsSeqFields v₁ v₂ v₃ refl) = mk&ₚ v₁ (mk&ₚ v₂ v₃ refl) refl

iso : Iso Rep AKIFieldsSeqFields
proj₁ iso = equivalent
proj₁ (proj₂ iso) (mk&ₚ fstₚ₁ (mk&ₚ fstₚ₂ sndₚ₁ refl) refl) = refl
proj₂ (proj₂ iso) (mkAKIFieldsSeqFields akeyid authcertiss authcertsn refl) = refl

@0 unambiguous : Unambiguous AKIFieldsSeqFields
unambiguous =
  isoUnambiguous iso
    (Unambiguous.option₃&₂
      (TLV.unambiguous OctetString.unambiguous) TLV.nonnesting TLV.nonempty
      (TLV.unambiguous GeneralName.GeneralNamesElems.unambiguous) TLV.nonnesting TLV.nonempty
      (TLV.unambiguous λ {xs} → Int.unambiguous{xs}) TLV.nonempty
      (TLV.noconfusion (λ ())) (TLV.noconfusion λ ()) (TLV.noconfusion λ ()))