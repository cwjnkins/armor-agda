open import Aeres.Binary
open import Aeres.Data.X690-DER.Strings.UniversalString.TCB
open import Aeres.Data.X690-DER.TLV
open import Aeres.Data.Unicode.UTF32
import      Aeres.Grammar.Parser
open import Aeres.Prelude

module Aeres.Data.X690-DER.Strings.UniversalString.Parser where

open Aeres.Grammar.Parser UInt8

parseUniversalString : Parser (Logging ∘ Dec) UniversalString
parseUniversalString =
  parseTLV _ "X690-DER: Strings: UniversalString: parse:" _ UTF32.parse
