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

--     val₁ : List UInt8
--     val₁ = # 4 ∷ # 6 ∷ # 3 ∷ # 4 ∷ # 6 ∷ # 160 ∷ # 0 ∷ [ # 0 ]

--     val₂ : List UInt8
--     val₂ = # 4 ∷ # 4 ∷ # 3 ∷ # 2 ∷ # 4 ∷ [ # 160 ]

--     val₃ : List UInt8
--     val₃ = # 4 ∷ # 4 ∷ # 3 ∷ # 2 ∷ # 6 ∷ [ # 160 ]

--     test₁ : KUFields val₁
--     test₁ = Success.value (toWitness {Q = Logging.val (runParser parseKUFields val₁)} tt)

--     test₂ : KUFields val₂
--     test₂ = Success.value (toWitness {Q = Logging.val (runParser parseKUFields val₂)} tt)

    -- test₃ : ¬ Success _ KUFields val₃
    -- test₃ = toWitnessFalse {Q = Logging.val (runParser parseKUFields val₃)}
