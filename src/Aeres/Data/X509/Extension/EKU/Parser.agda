{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.Extension.EKU.TCB
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.SequenceOf
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parser
open import Aeres.Prelude

module Aeres.Data.X509.Extension.EKU.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parser      UInt8

private
  here' = "X509: Extension: EKU"

parseEKUFields : Parser (Logging ∘ Dec) EKUFields
parseEKUFields =
  parseTLV _ here' _
    (parseExactLength TLV.nonnesting
      (tell $ here' String.++ ": underflow")
      (parseNonEmptySeq (here' String.++ ": elems") _ TLV.nonempty TLV.nonnesting parseOID))

-- private
--   module Test where

--     val₁ : List Dig
--     val₁ = # 4 ∷ # 12 ∷ # 48 ∷ # 10 ∷ # 6 ∷ # 8 ∷ # 43 ∷ # 6 ∷ # 1 ∷ # 5 ∷ # 5 ∷ # 7 ∷ # 3 ∷ [ # 1 ]

--     val₂ : List Dig
--     val₂ = # 4 ∷ # 22 ∷ # 48 ∷ # 20 ∷ # 6 ∷ # 8 ∷ # 43 ∷ # 6 ∷ # 1 ∷ # 5 ∷ # 5 ∷ # 7 ∷ # 3 ∷ # 1 ∷ # 6 ∷ # 8 ∷ # 43 ∷ # 6 ∷ # 1 ∷ # 5 ∷ # 5 ∷ # 7 ∷ # 3 ∷ [ # 2 ]

--     test₁ : X509.EKUFields val₁
--     test₁ = Success.value (toWitness {Q = Logging.val (runParser parseEKUFields val₁)} tt)

--     test₂ : X509.EKUFields val₂
--     test₂ = Success.value (toWitness {Q = Logging.val (runParser parseEKUFields val₂)} tt)
