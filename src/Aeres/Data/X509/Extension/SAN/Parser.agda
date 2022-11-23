{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.GeneralName
open import Aeres.Data.X509.Extension.SAN.TCB
open import Aeres.Data.X690-DER.SequenceOf
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Parser
open import Aeres.Prelude

module Aeres.Data.X509.Extension.SAN.Parser where

open Aeres.Grammar.Parser UInt8

private
  here' = "X509: Extension: SAN"

parseSANFields : Parser (Logging ∘ Dec) SANFields
parseSANFields =
  parseTLV _ here' _
    (parseExactLength TLV.nonnesting (tell $ here' String.++ ": underflow")
      parseGeneralNames)
