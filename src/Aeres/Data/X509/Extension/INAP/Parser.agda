{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.Extension.INAP.TCB
open import Aeres.Data.X690-DER.Int
open import Aeres.Data.X690-DER.OctetString.TCB
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Parser
open import Aeres.Prelude

module Aeres.Data.X509.Extension.INAP.Parser where

open Aeres.Grammar.Parser UInt8

private
  here' = "X509: Extension: INAP"

parseINAPFields : Parser (Logging ∘ Dec) INAPFields
parseINAPFields =
  parseTLV _ here' _
    λ n → parseExactLength TLV.nonnesting (tell $ here' String.++ ": underflow") parseInt n

