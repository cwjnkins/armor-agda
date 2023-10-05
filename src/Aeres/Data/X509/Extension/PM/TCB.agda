{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.OID.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Data.X690-DER.SequenceOf.TCB
import      Aeres.Grammar.Definitions
import Aeres.Grammar.Seq
open import Aeres.Prelude

module Aeres.Data.X509.Extension.PM.TCB where

open  Aeres.Grammar.Definitions              UInt8
open Aeres.Grammar.Seq                       UInt8

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

PolicyMapFieldsRep : @0 List UInt8 → Set
PolicyMapFieldsRep = &ₚ OID OID

RawPolicyMapFieldsRep : Raw PolicyMapFieldsRep
RawPolicyMapFieldsRep = Raw&ₚ RawOID RawOID

equivalentPolicyMapFields : Equivalent PolicyMapFieldsRep PolicyMapFields
proj₁ equivalentPolicyMapFields (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = mkPolicyMapFields fstₚ₁ sndₚ₁ bs≡
proj₂ equivalentPolicyMapFields (mkPolicyMapFields issuerDomainPolicy subjectDomainPolicy bs≡) = mk&ₚ issuerDomainPolicy subjectDomainPolicy bs≡

RawPolicyMapFields : Raw PolicyMapFields
RawPolicyMapFields =  Iso.raw equivalentPolicyMapFields RawPolicyMapFieldsRep

RawPMFields : Raw PMFields
RawPMFields = RawTLV _ (RawTLV _ (RawBoundedSequenceOf (RawTLV _ RawPolicyMapFields) 1))
