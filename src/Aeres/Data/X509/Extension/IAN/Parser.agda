{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.GeneralNames
open import Aeres.Data.X509.Extension.IAN.TCB
open import Aeres.Data.X690-DER.SequenceOf
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Parallel
import      Aeres.Grammar.Parser
open import Aeres.Prelude

module Aeres.Data.X509.Extension.IAN.Parser where

open Aeres.Grammar.Parallel UInt8
open Aeres.Grammar.Parser   UInt8

private
  here' = "X509: Extension: IAN"

parseIANFields : Parser (Logging ∘ Dec) IANFields
parseIANFields =
  parseTLV _ here' _
    (parseExactLength TLV.nosubstrings (tell $ here' String.++ ": underflow")
      parseGeneralNames)
