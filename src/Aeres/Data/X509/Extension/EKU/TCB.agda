{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.OID.TCB
open import Aeres.Data.X690-DER.SequenceOf.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
import Aeres.Grammar.Definitions
open import Aeres.Data.X690-DER.SequenceOf.TCB
open import Aeres.Prelude

module Aeres.Data.X509.Extension.EKU.TCB where

open Aeres.Grammar.Definitions UInt8

-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.2.1.12
--    id-ce-extKeyUsage OBJECT IDENTIFIER ::= { id-ce 37 }

--    ExtKeyUsageSyntax ::= SEQUENCE SIZE (1..MAX) OF KeyPurposeId

--    KeyPurposeId ::= OBJECT IDENTIFIER

EKUFieldsSeq : @0 List UInt8 → Set
EKUFieldsSeq xs = TLV Tag.Sequence (NonEmptySequenceOf OID) xs

EKUFields : @0 List UInt8 → Set
EKUFields xs = TLV Tag.OctetString EKUFieldsSeq xs

RawEKUFields : Raw EKUFields
RawEKUFields = RawTLV _ (RawTLV _ (RawBoundedSequenceOf RawOID 1))
