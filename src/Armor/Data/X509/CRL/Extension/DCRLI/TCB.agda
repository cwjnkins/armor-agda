open import Armor.Binary
open import Armor.Data.X690-DER.Int.TCB as Int
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions.NonMalleable
open import Armor.Prelude

module Armor.Data.X509.CRL.Extension.DCRLI.TCB where

open Armor.Grammar.Definitions.NonMalleable UInt8

 -- id-ce-deltaCRLIndicator OBJECT IDENTIFIER ::= { id-ce 27 }
 -- BaseCRLNumber ::= CRLNumber

-- enforce from 0..max in semantic check
DCRLIFields : @0 List UInt8 → Set
DCRLIFields xs = TLV Tag.OctetString Int xs
