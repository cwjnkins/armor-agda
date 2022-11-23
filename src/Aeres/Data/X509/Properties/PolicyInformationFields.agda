{-# OPTIONS --subtyping #-}


open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X690-DER
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
import      Aeres.Grammar.Properties
open import Aeres.Prelude

module Aeres.Data.X509.Properties.PolicyInformationFields where

open ≡-Reasoning
open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8
open Aeres.Grammar.Properties  UInt8

iso : Iso (&ₚ OID (Option PolicyQualifiersSeq))
          X509.PolicyInformationFields
proj₁ (proj₁ iso) (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = X509.mkPolicyInformationFields fstₚ₁ sndₚ₁ bs≡
proj₂ (proj₁ iso) (X509.mkPolicyInformationFields cpid cpqls bs≡) = mk&ₚ cpid cpqls bs≡
proj₁ (proj₂ iso) (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = refl
proj₂ (proj₂ iso) (X509.mkPolicyInformationFields cpid cpqls bs≡) = refl

@0 unambiguous : Unambiguous X509.PolicyInformationFields
unambiguous =
  isoUnambiguous iso
    (Unambiguous.unambiguous-&₁option₁
      OID.unambiguous TLV.nonnesting
      (TLV.unambiguous
        (SequenceOf.Bounded.unambiguous
          (TLV.unambiguous Qualifier.unambiguous) TLV.nonempty TLV.nonnesting))
      TLV.nonempty)
