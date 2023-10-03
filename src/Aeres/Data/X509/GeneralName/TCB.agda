{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.RDN.TCB
open import Aeres.Data.X690-DER.OID.TCB
open import Aeres.Data.X690-DER.OctetString.TCB
open import Aeres.Data.X690-DER.Strings
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Data.X690-DER.SequenceOf.TCB
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parallel.TCB
import      Aeres.Grammar.Sum.TCB
open import Aeres.Prelude

module Aeres.Data.X509.GeneralName.TCB where

open      Aeres.Grammar.Definitions              UInt8
open      Aeres.Grammar.Parallel.TCB             UInt8
open      Aeres.Grammar.Sum.TCB                  UInt8

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
DirName xs = TLV Tag.AA4 Name xs

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

GeneralNameRep = Sum OtherName
                   (Sum RfcName
                     (Sum DnsName
                       (Sum X400Address
                         (Sum DirName
                           (Sum EdipartyName
                             (Sum URI
                               (Sum IpAddress RegID)))))))

equivalent : Equivalent GeneralNameRep GeneralName
proj₁ equivalent (inj₁ x) = oname x
proj₁ equivalent (inj₂ (inj₁ x)) = rfcname x
proj₁ equivalent (inj₂ (inj₂ (inj₁ x))) = dnsname x
proj₁ equivalent (inj₂ (inj₂ (inj₂ (inj₁ x)))) = x400add x
proj₁ equivalent (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ x))))) = dirname x
proj₁ equivalent (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ x)))))) = ediname x
proj₁ equivalent (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ x))))))) = uri x
proj₁ equivalent (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ x)))))))) = ipadd x
proj₁ equivalent (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ x)))))))) = rid x
proj₂ equivalent (oname x) = inj₁ x
proj₂ equivalent (rfcname x) = inj₂ (inj₁ x)
proj₂ equivalent (dnsname x) = inj₂ (inj₂ (inj₁ x))
proj₂ equivalent (x400add x) = inj₂ (inj₂ (inj₂ (inj₁ x)))
proj₂ equivalent (dirname x) = inj₂ (inj₂ (inj₂ (inj₂ (inj₁ x))))
proj₂ equivalent (ediname x) = inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ x)))))
proj₂ equivalent (uri x) = inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ x))))))
proj₂ equivalent (ipadd x) = inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ x)))))))
proj₂ equivalent (rid x) = inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ x)))))))

RawGeneralNameRep : Raw GeneralNameRep
RawGeneralNameRep = RawSum (RawTLV _ RawOctetStringValue)
                      (RawSum (RawTLV _ RawIA5StringValue)
                        (RawSum (RawTLV _ RawIA5StringValue)
                          (RawSum (RawTLV _ RawOctetStringValue)
                            (RawSum (RawTLV _ RawName)
                              (RawSum (RawTLV _ RawOctetStringValue)
                                (RawSum (RawTLV _ RawIA5StringValue)
                                  (RawSum (RawTLV _ RawOctetStringValue)
                                           (RawTLV _ RawOIDValue))))))))

RawGeneralName : Raw GeneralName
RawGeneralName = Iso.raw equivalent RawGeneralNameRep

RawGeneralNames : Raw GeneralNames
RawGeneralNames = RawTLV _ (RawBoundedSequenceOf RawGeneralName 1)
