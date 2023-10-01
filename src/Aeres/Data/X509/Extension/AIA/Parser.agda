{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.Extension.AIA.AccessDesc
open import Aeres.Data.X509.Extension.AIA.TCB
open import Aeres.Data.X690-DER.SequenceOf
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Parallel
import      Aeres.Grammar.Parser
open import Aeres.Prelude

module Aeres.Data.X509.Extension.AIA.Parser where

open Aeres.Grammar.Parser   UInt8
open Aeres.Grammar.Parallel UInt8

private
  here' = "X509: Extension: AIA"

parseAIAFields : Parser (Logging ∘ Dec) AIAFields
parseAIAFields =
  parseTLV _ here' _ (parseExactLength TLV.nosubstrings (tell $ here' String.++ ": underflow")
    (parseNonEmptySeq (here' String.++ ": elems") _ TLV.nonempty TLV.nosubstrings parseAccessDesc))
