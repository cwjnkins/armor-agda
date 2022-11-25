{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.TCB
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Option
open import Aeres.Prelude

module Aeres.Data.X509.Extension.CertPolicy.PolicyInformation.TCB where

open Aeres.Grammar.Option UInt8

record PolicyInformationFields (@0 bs : List UInt8) : Set where
  constructor mkPolicyInformationFields
  field
    @0 {pid pqls} : List UInt8
    cpid : OID pid
    cpqls : Option PolicyQualifiersSeq pqls
    @0 bs≡  : bs ≡ pid ++ pqls

PolicyInformation : @0 List UInt8 → Set
PolicyInformation xs = TLV Tag.Sequence PolicyInformationFields xs
