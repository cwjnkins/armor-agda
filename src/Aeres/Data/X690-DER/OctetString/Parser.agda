open import Aeres.Binary
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Data.X690-DER.OctetString.TCB
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parallel
import      Aeres.Grammar.Parser
open import Aeres.Prelude

module Aeres.Data.X690-DER.OctetString.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parallel    UInt8
open Aeres.Grammar.Parser      UInt8

private
  here' = "X690-DER: OctetString"

parseValue : ∀ n → Parser (Logging ∘ Dec) (ExactLength OctetStringValue n)
parseValue = λ n → parseN n (tell $ here' String.++ " (value): underflow")

parse : Parser (Logging ∘ Dec) OctetString
parse = parseTLV Tag.OctetString here' OctetStringValue parseValue
