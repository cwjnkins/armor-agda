{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509
import      Aeres.Data.X509.Properties.Primitives as PrimProps
import      Aeres.Data.X509.Properties.TLV as TLVProps
open import Aeres.Prelude

module Aeres.Data.X509.Properties.PCFieldsSeqFields where

open Base256
open import Aeres.Grammar.Definitions Dig
open import Aeres.Grammar.Properties  Dig

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
      (TLVProps.unambiguous λ {xs} → PrimProps.IntegerValue.unambiguous{xs})  TLVProps.nonnesting TLVProps.nonempty
      (TLVProps.unambiguous λ {xs} → PrimProps.IntegerValue.unambiguous{xs}) TLVProps.nonempty (TLVProps.noconfusion λ ()))
