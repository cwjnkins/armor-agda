{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.Properties
open import Aeres.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.TCB
import      Aeres.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.TCB.OIDs as OIDs
open import Aeres.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.UserNotice
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.Sequence.DefinedByOID
open import Aeres.Data.X690-DER.SequenceOf.TCB
open import Aeres.Data.X690-DER.Strings
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parallel
import      Aeres.Grammar.Sum
open import Aeres.Prelude

module Aeres.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.Eq where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parallel    UInt8
open Aeres.Grammar.Sum         UInt8

instance
  eq≋CPS : Eq≋ CPSURIQualifier
  eq≋CPS =
    DefinedByOID.eq≋ _ λ _ →
      Parallel.eq≋Σₚ it λ _ →
        record
          { _≟_ = λ where
            ≋-refl ≋-refl → yes refl
          }

  eq≋UserNotice : Eq≋ UserNoticeQualifier
  eq≋UserNotice =
    DefinedByOID.eq≋ _ λ _ →
      Parallel.eq≋Σₚ it λ _ →
        record
          { _≟_ = λ where
            ≋-refl ≋-refl → yes refl
          }

  eq≋ : Eq≋ PolicyQualifierInfoFields
  eq≋ = Iso.isoEq≋ iso Sum.sumEq≋
