{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.Extension.SKI.TCB
open import Aeres.Data.X690-DER.OctetString
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parallel
import      Aeres.Grammar.Parser
open import Aeres.Prelude

module Aeres.Data.X509.Extension.SKI.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parallel    UInt8
open Aeres.Grammar.Parser      UInt8

private
  here' = "X509: Extension: SKI"

parseSKIFields : Parser (Logging ∘ Dec) SKIFields
parseSKIFields =
  parseTLV _ "SKI Fields" _
    (parseExactLength TLV.nosubstrings (tell $ here' String.++ ": underflow") OctetString.parse)

-- private
--   module Test where

--     val₁ : List Dig
--     val₁ = # 4 ∷ # 22 ∷ # 4 ∷ # 20 ∷ # 147 ∷ # 61 ∷ # 128 ∷ # 160 ∷ # 120 ∷ # 95 ∷ # 164 ∷ # 18 ∷ # 101 ∷ # 194 ∷ # 57 ∷ # 173 ∷ # 54 ∷ # 77 ∷ # 116 ∷ # 177 ∷ # 171 ∷ # 84 ∷ # 108 ∷ [ # 167 ]

--     test₁ : X509.SKIFields val₁
--     test₁ = Success.value (toWitness {Q = Logging.val (runParser parseSKIFields val₁)} tt)
