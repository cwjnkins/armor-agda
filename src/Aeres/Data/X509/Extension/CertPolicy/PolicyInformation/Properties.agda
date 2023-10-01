{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier
open import Aeres.Data.X509.Extension.CertPolicy.PolicyInformation.TCB
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.TLV
open import Aeres.Data.X690-DER.SequenceOf
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Seq
open import Aeres.Prelude

module Aeres.Data.X509.Extension.CertPolicy.PolicyInformation.Properties where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8
open Aeres.Grammar.Properties  UInt8
open Aeres.Grammar.Seq         UInt8

Rep = &ₚ OID (Option PolicyQualifiersSeq)

iso : Iso Rep PolicyInformationFields
proj₁ (proj₁ iso) (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = mkPolicyInformationFields fstₚ₁ sndₚ₁ bs≡
proj₂ (proj₁ iso) (mkPolicyInformationFields cpid cpqls bs≡) = mk&ₚ cpid cpqls bs≡
proj₁ (proj₂ iso) (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = refl
proj₂ (proj₂ iso) (mkPolicyInformationFields cpid cpqls bs≡) = refl

equiv = proj₁ iso

@0 unambiguous : Unambiguous PolicyInformationFields
unambiguous =
  Iso.unambiguous iso
    (Unambiguous.unambiguous-&₁option₁
      OID.unambiguous TLV.nosubstrings
      (TLV.unambiguous
        (SequenceOf.Bounded.unambiguous
          (TLV.unambiguous Qualifier.unambiguous) TLV.nonempty TLV.nosubstrings))
      TLV.nonempty)
