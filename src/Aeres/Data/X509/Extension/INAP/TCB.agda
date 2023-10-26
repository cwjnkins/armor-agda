{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.Int.TCB
open import Aeres.Data.X690-DER.OctetString.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
open import Aeres.Prelude

module Aeres.Data.X509.Extension.INAP.TCB where

open      Aeres.Grammar.Definitions  UInt8

-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.2.1.14
--    id-ce-inhibitAnyPolicy OBJECT IDENTIFIER ::=  { id-ce 54 }

--    InhibitAnyPolicy ::= SkipCerts

--    SkipCerts ::= INTEGER (0..MAX)
   
INAPFields : @0 List UInt8 → Set
INAPFields xs = TLV Tag.OctetString Int xs

RawINAPFields : Raw INAPFields
RawINAPFields = RawTLV _ RawInt
