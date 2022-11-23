{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.Extension.CertPolicy.PolicyInformation.Properties
open import Aeres.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier
open import Aeres.Data.X509.Extension.CertPolicy.PolicyInformation.TCB
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.TLV
open import Aeres.Data.X690-DER.SequenceOf
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
open import Aeres.Prelude

module Aeres.Data.X509.Extension.CertPolicy.PolicyInformation.Eq where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8

instance
  eq≋ : Eq≋ PolicyInformationFields
  eq≋ = isoEq≋ iso (eq≋&ₚ it it)
    where
      instance
        e : Eq≋ (NonEmptySequenceOf PolicyQualifierInfo)
        e = SequenceOf.BoundedSequenceOfEq≋
