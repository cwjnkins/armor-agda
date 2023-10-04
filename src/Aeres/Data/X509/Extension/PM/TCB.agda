{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.OID.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Data.X690-DER.SequenceOf.TCB
import      Aeres.Grammar.Definitions
open import Aeres.Prelude

module Aeres.Data.X509.Extension.PM.TCB where

open  Aeres.Grammar.Definitions              UInt8

record PolicyMapFields (@0 bs : List UInt8) : Set where
  constructor mkPolicyMapFields
  field
    @0 {iss sub} : List UInt8
    issuerDomainPolicy : OID iss
    subjectDomainPolicy : OID sub
    @0 bs≡  : bs ≡ iss ++ sub

PolicyMap : @0 List UInt8 → Set
PolicyMap xs = TLV Tag.Sequence PolicyMapFields xs

PMFieldsSeq : @0 List UInt8 → Set
PMFieldsSeq xs = TLV Tag.Sequence (NonEmptySequenceOf PolicyMap) xs

PMFields : @0 List UInt8 → Set
PMFields xs = TLV Tag.OctetString  PMFieldsSeq xs

postulate
  RawPolicyMapFields : Raw PolicyMapFields

RawPMFields : Raw PMFields
RawPMFields = RawTLV _ (RawTLV _ (RawBoundedSequenceOf (RawTLV _ RawPolicyMapFields) 1))
