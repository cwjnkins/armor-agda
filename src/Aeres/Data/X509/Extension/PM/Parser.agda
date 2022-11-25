{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.Extension.PM.Properties
open import Aeres.Data.X509.Extension.PM.TCB
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Data.X690-DER.SequenceOf
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parser
open import Aeres.Prelude

module Aeres.Data.X509.Extension.PM.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parser      UInt8

private
  here' = "X509: Extension: PM"

parsePolicyMapFields : Parser (Logging ∘ Dec) PolicyMapFields
parsePolicyMapFields =
  parseEquivalent equivalent
    (parse& TLV.nonnesting parseOID parseOID)

parsePMFields : Parser (Logging ∘ Dec) PMFields
parsePMFields =
  parseTLV _ here' _
    (parseExactLength  TLV.nonnesting (tell $ here' String.++ ": underflow")
      (parseNonEmptySeq here' _ TLV.nonempty TLV.nonnesting
        (parseTLV _ here' _
          (λ n → parseExactLength nonnesting (tell $ here' String.++ ": underflow") parsePolicyMapFields n))))
