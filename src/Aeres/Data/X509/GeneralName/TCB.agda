{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.IA5String.TCB
open import Aeres.Data.X509.RDN.TCB
open import Aeres.Data.X690-DER.OID.TCB
open import Aeres.Data.X690-DER.OctetString.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Data.X690-DER.SequenceOf.TCB
open import Aeres.Prelude

module Aeres.Data.X509.GeneralName.TCB where

--- we do not support OtherName since very rarely used
OtherName : @0 List UInt8 → Set
OtherName xs = TLV Tag.AA0 OctetStringValue xs --abstracted

RfcName : @0 List UInt8 → Set
RfcName xs = TLV Tag.A81 IA5StringValue xs

DnsName : @0 List UInt8 → Set
DnsName xs = TLV Tag.A82 IA5StringValue xs

--- we do not support X400Address since very rarely used
X400Address : @0 List UInt8 → Set
X400Address xs = TLV Tag.AA3 OctetStringValue xs --abstracted

DirName : @0 List UInt8 → Set
DirName xs = TLV Tag.AA4 RDNSeq xs

--- we do not support EdipartyName since very rarely used
EdipartyName : @0 List UInt8 → Set
EdipartyName xs = TLV Tag.AA5 OctetStringValue xs --abstracted

URI : @0 List UInt8 → Set
URI xs = TLV Tag.A86 IA5StringValue xs

IpAddress : @0 List UInt8 → Set
IpAddress xs = TLV Tag.A87 OctetStringValue xs

RegID : @0 List UInt8 → Set
RegID xs = TLV Tag.A88 OIDValue xs

data GeneralName : @0 List UInt8 → Set where
  oname : ∀ {@0 bs} → OtherName bs → GeneralName bs
  rfcname : ∀ {@0 bs} → RfcName bs → GeneralName bs
  dnsname : ∀ {@0 bs} → DnsName bs → GeneralName bs
  x400add : ∀ {@0 bs} → X400Address bs → GeneralName bs
  dirname : ∀ {@0 bs} → DirName bs → GeneralName bs
  ediname : ∀ {@0 bs} → EdipartyName bs → GeneralName bs
  uri : ∀ {@0 bs} → URI bs → GeneralName bs
  ipadd : ∀ {@0 bs} → IpAddress bs → GeneralName bs
  rid : ∀ {@0 bs} → RegID bs → GeneralName bs

GeneralNamesElems = NonEmptySequenceOf GeneralName
GeneralNames = TLV Tag.Sequence GeneralNamesElems
