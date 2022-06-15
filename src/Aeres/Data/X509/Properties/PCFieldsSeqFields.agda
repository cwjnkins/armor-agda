{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509
import      Aeres.Data.X509.Properties.Primitives as PrimProps
open import Aeres.Data.X690-DER
open import Aeres.Prelude

module Aeres.Data.X509.Properties.PCFieldsSeqFields where

open Base256
open import Aeres.Grammar.Definitions UInt8
open import Aeres.Grammar.Properties  UInt8

equivalent : Equivalent (&ₚ (Option X509.RequireExplicitPolicy) (Option X509.InhibitPolicyMapping)) X509.PCFieldsSeqFields
proj₁ equivalent (mk&ₚ v₁ v₂ refl) = X509.mkPCFieldsSeqFields v₁ v₂ refl
proj₂ equivalent (X509.mkPCFieldsSeqFields v₁ v₂ refl) = mk&ₚ v₁ v₂ refl

iso : Iso (&ₚ (Option X509.RequireExplicitPolicy) (Option X509.InhibitPolicyMapping)) X509.PCFieldsSeqFields
proj₁ iso = equivalent
proj₁ (proj₂ iso) (mk&ₚ fstₚ₁ sndₚ₁ refl) = refl
proj₂ (proj₂ iso) (X509.mkPCFieldsSeqFields require inhibit refl) = refl

@0 unambiguous : Unambiguous X509.PCFieldsSeqFields
unambiguous =
  isoUnambiguous iso
    (Unambiguous.option₂&₁
      (TLV.unambiguous λ {xs} → PrimProps.IntegerValue.unambiguous{xs})  TLV.nonnesting TLV.nonempty
      (TLV.unambiguous λ {xs} → PrimProps.IntegerValue.unambiguous{xs}) TLV.nonempty (TLV.noconfusion λ ()))
