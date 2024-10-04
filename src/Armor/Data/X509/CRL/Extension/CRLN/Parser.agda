open import Armor.Binary
open import Armor.Data.X509.CRL.Extension.CRLN.TCB
open import Armor.Data.X690-DER.Int
open import Armor.Data.X690-DER.TLV
import      Armor.Grammar.Definitions
import      Armor.Grammar.Parallel
import      Armor.Grammar.Parser
open import Armor.Prelude

module Armor.Data.X509.CRL.Extension.CRLN.Parser where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Parallel    UInt8
open Armor.Grammar.Parser      UInt8

private
  here' = "X509: CRL: Extension: CRLN"

parseCRLNFields : Parser (Logging ∘ Dec) CRLNFields
parseCRLNFields =
  parseTLV _ "CRLN Fields" _
    (parseExactLength TLV.nosubstrings (tell $ here' String.++ ": underflow") (Int.parse here'))
