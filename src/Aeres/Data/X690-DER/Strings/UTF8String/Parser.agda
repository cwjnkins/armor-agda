open import Aeres.Binary
open import Aeres.Data.Unicode.UTF8
open import Aeres.Data.X690-DER.Strings.UTF8String.TCB
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Parser
open import Aeres.Prelude

module Aeres.Data.X690-DER.Strings.UTF8String.Parser where

open Aeres.Grammar.Parser UInt8

private
  here' = "X690-DER: Strings: UTF8String: parse"

parseUTF8String : Parser (Logging ∘ Dec) UTF8String
parseUTF8String =
  parseTLV Tag.UTF8String here' _ parseUTF8
