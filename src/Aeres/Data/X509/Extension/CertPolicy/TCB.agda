{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.Extension.CertPolicy.PolicyInformation.TCB
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.SequenceOf.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Prelude

module Aeres.Data.X509.Extension.CertPolicy.TCB where

CertPolFieldsSeq : @0 List UInt8 → Set
CertPolFieldsSeq = TLV Tag.Sequence (NonEmptySequenceOf PolicyInformation)

CertPolFields : @0 List UInt8 → Set
CertPolFields xs = TLV Tag.OctetString  CertPolFieldsSeq xs
