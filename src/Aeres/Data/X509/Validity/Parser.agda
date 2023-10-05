{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.Validity.TCB
open import Aeres.Data.X509.Validity.Time
open import Aeres.Data.X509.Validity.Properties
open import Aeres.Data.X690-DER
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parallel
import      Aeres.Grammar.Parser
import      Aeres.Grammar.Seq
open import Aeres.Prelude

module Aeres.Data.X509.Validity.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parallel    UInt8
open Aeres.Grammar.Parser      UInt8
open Aeres.Grammar.Seq         UInt8

module parseValidityFields where
  here' = "X509: Validity"

  parseValidityFields : Parser (Logging ∘ Dec) ValidityFields
  parseValidityFields =
    parseEquivalent equivalent
      (parse& Time.nosubstrings Time.parse Time.parse)

open parseValidityFields public using (parseValidityFields)

parseValidity : Parser (Logging ∘ Dec) Validity
parseValidity =
  parseTLV _ parseValidityFields.here' _
    (parseExactLength nosubstrings
      (tell $ parseValidityFields.here' String.++ ": length mismatch")
      parseValidityFields)

-- private
--   module Test where

--     Validity₁ : List Dig
--     Validity₁ = Tag.Sequence ∷ # 32 ∷ # Tag.GeneralizedTime ∷ # 15 ∷ # 50 ∷ # 56 ∷ # 52 ∷ # 49 ∷ # 48 ∷ # 54 ∷ # 50 ∷ # 52 ∷ # 49 ∷ # 56 ∷ # 51 ∷ # 54 ∷ # 53 ∷ # 52 ∷ # 90 ∷ # Tag.UTCTime ∷ # 13 ∷ # 57 ∷ # 55 ∷ # 48 ∷ # 53 ∷ # 51 ∷ # 48 ∷ # 49 ∷ # 52 ∷ # 52 ∷ # 56 ∷ # 50 ∷ # 50 ∷ [ # 90 ]

--     test₁ : Validity Validity₁
--     test₁ = Success.value (toWitness {Q = Logging.val (runParser parseValidity Validity₁)} tt)
