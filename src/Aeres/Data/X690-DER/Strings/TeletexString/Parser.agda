open import Aeres.Binary
open import Aeres.Data.X690-DER.OctetString
open import Aeres.Data.X690-DER.Strings.TeletexString.TCB
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Parser
open import Aeres.Prelude

module Aeres.Data.X690-DER.Strings.TeletexString.Parser where

open Aeres.Grammar.Parser UInt8

private
  here' = "X690-DER: Strings: TeletexString: parse"

parseTeletexString : Parser (Logging ∘ Dec) TeletexString
parseTeletexString =
  parseTLV Tag.TeletexString here' _ OctetString.parseValue
