{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.TLV
open import Aeres.Data.X690-DER.Tag
open import Aeres.Data.X690-DER.OctetString.TCB
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parser
open import Aeres.Prelude

module Aeres.Data.X690-DER.OctetString.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parser      UInt8

parseOctetStringValue : ∀ n → Parser (Logging ∘ Dec) (ExactLength OctetStringValue n)
parseOctetStringValue = λ n → parseN n (tell $ here' String.++ ": underflow")
  where here' = "parseOctetStringValue"

parseOctetString : Parser (Logging ∘ Dec) OctetString
parseOctetString = parseTLV Tag.OctetString  "Octet string" OctetStringValue parseOctetStringValue
  where here' = "parseOctetString"


