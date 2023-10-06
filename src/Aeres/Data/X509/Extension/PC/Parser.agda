{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.Extension.PC.TCB
open import Aeres.Data.X509.Extension.PC.Properties
open import Aeres.Data.X690-DER.Int
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
import      Aeres.Grammar.Parallel
import      Aeres.Grammar.Parser
open import Aeres.Prelude

module Aeres.Data.X509.Extension.PC.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8
open Aeres.Grammar.Parallel    UInt8
open Aeres.Grammar.Parser      UInt8

private
  here' = "X509: Extension: PC"

parsePCFields : Parser (Logging ∘ Dec) PCFields
parsePCFields =
  parseTLV _ here' _
    (parseExactLength TLV.nosubstrings (tell $ here' String.++ ": underflow")
      (parseTLV _ here' _ helper))
  where
  helper : (n : ℕ) → Parser (Logging ∘ Dec) (ExactLength (PCFieldsSeqFields) n)
  helper n =
    parseEquivalent (Parallel.equivalent₁ equivalentPCFieldsSeqFields)
      (Option.parseOption₂ TLV.nosubstrings TLV.nosubstrings (TLV.noconfusion (λ ()))
        (parseTLV _ (here' String.++ ": require explicit policy") _ Int.parseValue)
        (parseTLV _ (here' String.++ ": inhibit policy mapping") _ Int.parseValue)
        (tell $ here' String.++ ": underflow") n)
