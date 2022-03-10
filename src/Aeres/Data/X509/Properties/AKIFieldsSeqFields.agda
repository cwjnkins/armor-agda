{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509
import      Aeres.Data.X509.Properties.GeneralName as GeneralNameProps
import      Aeres.Data.X509.Properties.OctetstringValue as OSProps
import      Aeres.Data.X509.Properties.Primitives as PrimProps
import      Aeres.Data.X509.Properties.TLV as TLVProps
open import Aeres.Prelude

module Aeres.Data.X509.Properties.AKIFieldsSeqFields where

open Base256
open import Aeres.Grammar.Definitions Dig
open import Aeres.Grammar.Properties  Dig

equivalent : Equivalent (&ₚ (Option X509.AKIKeyId) (&ₚ (Option X509.AKIAuthCertIssuer) (Option X509.AKIAuthCertSN))) X509.AKIFieldsSeqFields
proj₁ equivalent (mk&ₚ v₁ (mk&ₚ v₂ v₃ refl) refl) = X509.mkAKIFieldsSeqFields v₁ v₂ v₃ refl
proj₂ equivalent (X509.mkAKIFieldsSeqFields v₁ v₂ v₃ refl) = mk&ₚ v₁ (mk&ₚ v₂ v₃ refl) refl

iso : Iso (&ₚ (Option X509.AKIKeyId) (&ₚ (Option X509.AKIAuthCertIssuer) (Option X509.AKIAuthCertSN))) X509.AKIFieldsSeqFields
proj₁ iso = equivalent
proj₁ (proj₂ iso) (mk&ₚ fstₚ₁ (mk&ₚ fstₚ₂ sndₚ₁ refl) refl) = refl
proj₂ (proj₂ iso) (X509.mkAKIFieldsSeqFields akeyid authcertiss authcertsn refl) = refl

@0 unambiguous : Unambiguous X509.AKIFieldsSeqFields
unambiguous =
  isoUnambiguous iso
    (Unambiguous.option₃&₂
      (TLVProps.unambiguous OSProps.unambiguous) TLVProps.nonnesting TLVProps.nonempty
      (TLVProps.unambiguous GeneralNameProps.GeneralNamesElems.unambiguous) TLVProps.nonnesting TLVProps.nonempty
      (TLVProps.unambiguous λ {xs} → PrimProps.IntegerValue.unambiguous{xs}) TLVProps.nonempty
      (TLVProps.noconfusion (λ ())) (TLVProps.noconfusion λ ()) (TLVProps.noconfusion λ ()))
