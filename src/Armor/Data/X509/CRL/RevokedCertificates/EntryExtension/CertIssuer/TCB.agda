{-# OPTIONS --erasure #-}
open import Armor.Binary
open import Armor.Data.X509.GeneralNames.TCB
open import Armor.Data.X690-DER.Int.TCB as Int
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions.NonMalleable
open import Armor.Prelude

module Armor.Data.X509.CRL.RevokedCertificates.EntryExtension.CertIssuer.TCB where

open Armor.Grammar.Definitions.NonMalleable UInt8

-- id-ce-certificateIssuer   OBJECT IDENTIFIER ::= { id-ce 29 }
-- CertificateIssuer ::=     GeneralNames

CertIssuerFields : @0 List UInt8 → Set
CertIssuerFields xs = TLV Tag.OctetString GeneralNames xs

RawCertIssuerFields : Raw CertIssuerFields
RawCertIssuerFields = RawTLV _ RawGeneralNames
