{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.GeneralName.TCB
open import Aeres.Data.X690-DER.Int.TCB
open import Aeres.Data.X690-DER.OctetString.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions.NonMalleable
import      Aeres.Grammar.Option
open import Aeres.Prelude

module Aeres.Data.X509.Extension.AKI.TCB where

open Aeres.Grammar.Option UInt8
open Aeres.Grammar.Definitions.NonMalleable UInt8

AKIKeyId : @0 List UInt8 → Set
AKIKeyId = TLV Tag.A80 OctetStringValue

AKIAuthCertIssuer : @0 List UInt8 → Set
AKIAuthCertIssuer = TLV Tag.AA1 GeneralNamesElems

AKIAuthCertSN : @0 List UInt8 → Set
AKIAuthCertSN = TLV Tag.A82 IntegerValue

record AKIFieldsSeqFields (@0 bs : List UInt8) : Set where
  constructor mkAKIFieldsSeqFields
  field
    @0 {akid ci csn} : List UInt8
    akeyid : Option AKIKeyId akid
    authcertiss : Option AKIAuthCertIssuer ci
    authcertsn : Option AKIAuthCertSN csn
    @0 bs≡  : bs ≡ akid ++ ci ++ csn

AKIFieldsSeq : @0 List UInt8 → Set
AKIFieldsSeq = TLV Tag.Sequence AKIFieldsSeqFields

AKIFields : @0 List UInt8 → Set
AKIFields = TLV Tag.OctetString AKIFieldsSeq

RawAKIFieldsSeqFields : Raw AKIFieldsSeqFields
RawAKIFieldsSeqFields = {!Raw&ₚ!}

RawAKIFields : Raw AKIFields 
RawAKIFields = RawTLV _ (RawTLV _ RawAKIFieldsSeqFields)
