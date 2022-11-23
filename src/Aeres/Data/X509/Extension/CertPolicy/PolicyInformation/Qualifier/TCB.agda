{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.AlgorithmIdentifier.TCB
import      Aeres.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.TCB.OIDs as OIDs
open import Aeres.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.UserNotice.TCB
open import Aeres.Data.X509.IA5String.TCB
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.SequenceOf.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
open import Aeres.Prelude

module Aeres.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.TCB where

open Aeres.Grammar.Definitions UInt8

CPSURIQualifierParam : ∀ {@0 bs} → OID bs → @0 List UInt8 → Set
CPSURIQualifierParam o =
     IA5String
  ×ₚ const (_≋_{A = OIDValue} (TLV.val o) OIDs.CPSURI)

CPSURIQualifier = AlgorithmIdentifierFields CPSURIQualifierParam

UserNoticeQualifierParam : ∀ {@0 bs} → OID bs → @0 List UInt8 → Set
UserNoticeQualifierParam o =
     UserNotice
  ×ₚ const (_≋_{A = OIDValue} (TLV.val o) OIDs.UserNotice)

UserNoticeQualifier = AlgorithmIdentifierFields UserNoticeQualifierParam

data PolicyQualifierInfoFields : @0 List UInt8 → Set where
  cpsURI : ∀ {@0 bs} → CPSURIQualifier bs → PolicyQualifierInfoFields bs
  userNotice : ∀ {@0 bs} → UserNoticeQualifier bs → PolicyQualifierInfoFields bs

PolicyQualifierInfo : @0 List UInt8 → Set
PolicyQualifierInfo xs = TLV Tag.Sequence PolicyQualifierInfoFields xs

PolicyQualifiersSeq : @0 List UInt8 → Set
PolicyQualifiersSeq xs = TLV Tag.Sequence (NonEmptySequenceOf PolicyQualifierInfo) xs
