{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.AlgorithmIdentifier
open import Aeres.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.TCB
import      Aeres.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.TCB.OIDs as OIDs
open import Aeres.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.UserNotice
open import Aeres.Data.X509.IA5String
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.SequenceOf.TCB
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Sum
open import Aeres.Prelude

module Aeres.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.Properties where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Sum         UInt8

module CPSURIQualifier where

  @0 unambiguous : Unambiguous CPSURIQualifier
  unambiguous =
    AlgorithmIdentifier.unambiguous CPSURIQualifierParam
      λ o → unambiguous×ₚ (TLV.unambiguous IA5String.unambiguous) λ where ≋-refl ≋-refl → refl

module UserNoticeQualifier where
  @0 unambiguous : Unambiguous UserNoticeQualifier
  unambiguous =
    AlgorithmIdentifier.unambiguous UserNoticeQualifierParam
      λ o → unambiguous×ₚ (TLV.unambiguous UserNotice.unambiguous) λ where ≋-refl ≋-refl → refl

equivalent : Equivalent (Sum CPSURIQualifier UserNoticeQualifier) PolicyQualifierInfoFields
proj₁ equivalent (Sum.inj₁ x) = cpsURI x
proj₁ equivalent (Sum.inj₂ x) = userNotice x
proj₂ equivalent (cpsURI x) = Sum.inj₁ x
proj₂ equivalent (userNotice x) = Sum.inj₂ x

iso : Iso (Sum CPSURIQualifier UserNoticeQualifier) PolicyQualifierInfoFields
proj₁ iso = equivalent
proj₁ (proj₂ iso) (Sum.inj₁ x) = refl
proj₁ (proj₂ iso) (Sum.inj₂ x) = refl
proj₂ (proj₂ iso) (cpsURI x) = refl
proj₂ (proj₂ iso) (userNotice x) = refl

@0 nonnesting : NonNesting PolicyQualifierInfoFields
nonnesting =
  equivalent-nonnesting equivalent
    (nonnestingSum{A = CPSURIQualifier}{B = UserNoticeQualifier}
      (equivalent-nonnesting (AlgorithmIdentifier.equiv _)
        (nonnesting&ₚᵈ TLV.nonnesting OID.unambiguous
          (λ _ → nonnesting×ₚ₁ TLV.nonnesting)))
      (equivalent-nonnesting (AlgorithmIdentifier.equiv _)
        (nonnesting&ₚᵈ TLV.nonnesting OID.unambiguous
          (λ a → nonnesting×ₚ₁ TLV.nonnesting)))
      (AlgorithmIdentifier.noConfusionFieldsParam CPSURIQualifierParam
        λ where
          o (mk×ₚ _ ≋-refl refl) (mk×ₚ fstₚ₂ (mk≋ () _) refl)))

@0 unambiguous : Unambiguous PolicyQualifierInfoFields
unambiguous =
  isoUnambiguous iso
    (unambiguousSum CPSURIQualifier.unambiguous UserNoticeQualifier.unambiguous
      (AlgorithmIdentifier.noConfusionFieldsParam CPSURIQualifierParam
        λ where
          o (mk×ₚ _ ≋-refl refl) (mk×ₚ fstₚ₂ (mk≋ () _) refl)))
