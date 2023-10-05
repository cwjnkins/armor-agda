{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.TLV
open import Aeres.Data.X690-DER.Time.GeneralizedTime.Properties
open import Aeres.Data.X690-DER.Time.GeneralizedTime.TCB
open import Aeres.Data.X690-DER.Time.MDHMS
open import Aeres.Data.X690-DER.Time.TimeType
open import Aeres.Data.X690-DER.Time.Year
import      Aeres.Grammar.Parallel
import      Aeres.Grammar.Parser
import      Aeres.Grammar.Seq
open import Aeres.Prelude

module Aeres.Data.X690-DER.Time.GeneralizedTime.Parser where

open Aeres.Grammar.Parallel UInt8
open Aeres.Grammar.Parser   UInt8
open Aeres.Grammar.Seq      UInt8

private
  here' = "X690-DER: Generalized Time"

parseFields : Parser (Logging ∘ Dec) GeneralizedTimeFields
parseFields = parseEquivalent equivalent p
  where
  p : Parser (Logging ∘ Dec) GeneralizedTimeFieldsRep
  p =  parse& (Seq.nosubstrings TimeType.nosubstrings MDHMS.nosubstrings)
      (parse& TimeType.nosubstrings Year.parse₄ MDHMS.parse)
      (parseLit (tell $ here' String.++ ": underflow (Z)") (tell $ here' String.++ ": mismatch (Z)") [ # 'Z' ])

parse : Parser (Logging ∘ Dec) GeneralizedTime
parse = parseTLV _ here' _
          (parseExactLength nosubstrings
            (tell $ here' String.++ " (fields): length mismatch")
            parseFields)
