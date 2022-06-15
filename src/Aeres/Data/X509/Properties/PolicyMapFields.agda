{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X690-DER
open import Aeres.Prelude

module Aeres.Data.X509.Properties.PolicyMapFields where

open Base256
open import Aeres.Grammar.Definitions Dig
open import Aeres.Grammar.Properties  Dig

equivalent : Equivalent (&ₚ OID OID) X509.PolicyMapFields
proj₁ equivalent (mk&ₚ v₁ v₂ refl) = X509.mkPolicyMapFields v₁ v₂ refl
proj₂ equivalent (X509.mkPolicyMapFields v₁ v₂ refl) = mk&ₚ v₁ v₂ refl

iso : Iso (&ₚ OID OID) X509.PolicyMapFields
proj₁ iso = equivalent
proj₁ (proj₂ iso) (mk&ₚ fstₚ₁ sndₚ₁ refl) = refl
proj₂ (proj₂ iso) (X509.mkPolicyMapFields issuerDomainPolicy subjectDomainPolicy refl) = refl


@0 unambiguous : Unambiguous X509.PolicyMapFields
unambiguous =
  isoUnambiguous iso
    (unambiguous&ₚ OID.unambiguous TLV.nonnesting OID.unambiguous)


@0 nonnesting : NonNesting X509.PolicyMapFields
nonnesting x x₁ x₂ = NonNesting&ₚ TLV.nonnesting TLV.nonnesting x (proj₂ equivalent x₁) (proj₂ equivalent x₂)
