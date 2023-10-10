{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.Extension.PM.Properties
open import Aeres.Data.X509.Extension.PM.TCB
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Data.X690-DER.SequenceOf
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parallel
import      Aeres.Grammar.Parser
import      Aeres.Grammar.Seq
open import Aeres.Prelude

module Aeres.Data.X509.Extension.PM.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parallel    UInt8
open Aeres.Grammar.Parser      UInt8
open Aeres.Grammar.Seq         UInt8

private
  here' = "X509: Extension: PM"

parsePolicyMapFields : Parser (Logging ∘ Dec) PolicyMapFields
parsePolicyMapFields =
  parseEquivalent equivalentPolicyMapFields
    (parse& TLV.nosubstrings parseOID parseOID)

parsePMFields : Parser (Logging ∘ Dec) PMFields
parsePMFields =
  parseTLV _ here' _
    (parseExactLength  TLV.nosubstrings (tell $ here' String.++ ": underflow")
      (parseNonEmptySeq here' _ TLV.nonempty TLV.nosubstrings
        (parseTLV _ here' _
          (λ n → parseExactLength nosubstrings (tell $ here' String.++ ": underflow") parsePolicyMapFields n))))
