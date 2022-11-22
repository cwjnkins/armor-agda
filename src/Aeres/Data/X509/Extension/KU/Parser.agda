{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X509.Extension.KU.TCB
open import Aeres.Data.X690-DER.BitString
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parser

module Aeres.Data.X509.Extension.KU.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parser      UInt8

private
  here' = "X509: Extension: KU"

parseKUFields : Parser (Logging ∘ Dec) KUFields
parseKUFields =
  parseTLV _ here' _
    (parseExactLength TLV.nonnesting (tell $ here' String.++ ": underflow")
      parseBitstring)

-- private
--   module Test where

--     val₁ : List Dig
--     val₁ = # 4 ∷ # 4 ∷ # 3 ∷ # 2 ∷ # 5 ∷ [ # 160 ]

--     val₂ : List Dig
--     val₂ = # 4 ∷ # 4 ∷ # 3 ∷ # 2 ∷ # 4 ∷ [ # 160 ]

--     val₃ : List Dig
--     val₃ = # 4 ∷ # 4 ∷ # 3 ∷ # 2 ∷ # 6 ∷ [ # 160 ]

--     test₁ : X509.KUFields val₁
--     test₁ = Success.value (toWitness {Q = Logging.val (runParser parseKUFields val₁)} tt)

--     test₂ : X509.KUFields val₂
--     test₂ = Success.value (toWitness {Q = Logging.val (runParser parseKUFields val₂)} tt)

--     test₃ : ¬ Success _ X509.KUFields val₃
--     test₃ = toWitnessFalse {Q = Logging.val (runParser parseKUFields val₃)} tt
