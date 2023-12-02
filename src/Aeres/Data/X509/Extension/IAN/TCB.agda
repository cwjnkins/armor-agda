open import Aeres.Binary
open import Aeres.Data.X509.GeneralNames.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions.NonMalleable
open import Aeres.Prelude

module Aeres.Data.X509.Extension.IAN.TCB where

open Aeres.Grammar.Definitions.NonMalleable UInt8

-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.2.1.7
--    id-ce-issuerAltName OBJECT IDENTIFIER ::=  { id-ce 18 }

--    IssuerAltName ::= GeneralNames
   
IANFields : @0 List UInt8 → Set
IANFields xs = TLV Tag.OctetString GeneralNames xs

RawIANFields : Raw IANFields
RawIANFields = RawTLV _ RawGeneralNames
