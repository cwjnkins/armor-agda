open import Armor.Binary
open import Armor.Data.X690-DER.Int.TCB as Int
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions.NonMalleable
open import Armor.Prelude

module Armor.Data.X509.CRL.Extension.CRLN.TCB where

open Armor.Grammar.Definitions.NonMalleable UInt8

-- id-ce-cRLNumber OBJECT IDENTIFIER ::= { id-ce 20 }
-- CRLNumber ::= INTEGER (0..MAX)

-- enforce from 0 in semantic check
CRLNFields : @0 List UInt8 → Set
CRLNFields xs = TLV Tag.OctetString Int xs

RawCRLNFields : Raw CRLNFields
RawCRLNFields = RawTLV _ RawInt
