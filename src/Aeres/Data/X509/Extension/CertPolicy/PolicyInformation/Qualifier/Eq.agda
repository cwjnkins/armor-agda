{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.AlgorithmIdentifier
open import Aeres.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.Properties
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

module Aeres.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.Eq where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Sum         UInt8

instance
  eq≋CPS : Eq≋ CPSURIQualifier
  eq≋CPS =
    AlgorithmIdentifier.eq≋ _ λ _ →
      eq≋Σₚ it λ _ →
        record
          { _≟_ = λ where
            ≋-refl ≋-refl → yes refl
          }

  eq≋UserNotice : Eq≋ UserNoticeQualifier
  eq≋UserNotice =
    AlgorithmIdentifier.eq≋ _ λ _ →
      eq≋Σₚ it λ _ →
        record
          { _≟_ = λ where
            ≋-refl ≋-refl → yes refl
          }

  eq≋ : Eq≋ PolicyQualifierInfoFields
  eq≋ = isoEq≋ iso sumEq≋
