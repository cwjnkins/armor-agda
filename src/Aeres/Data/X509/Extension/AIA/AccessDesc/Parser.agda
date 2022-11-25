{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.Extension.AIA.AccessDesc.AccessMethod
open import Aeres.Data.X509.Extension.AIA.AccessDesc.Properties
open import Aeres.Data.X509.Extension.AIA.AccessDesc.TCB
open import Aeres.Data.X509.GeneralName
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parser
open import Aeres.Prelude

module Aeres.Data.X509.Extension.AIA.AccessDesc.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parser      UInt8

private
  here' = "X509: Extension: AIA: AccessDesc"

parseAccessDescFields : ∀ n → Parser (Logging ∘ Dec) (ExactLength AccessDescFields n)
parseAccessDescFields n =
  parseExactLength nonnesting (tell $ here' String.++ ": underflow")
    (parseEquivalent equivalent (parse& TLV.nonnesting parseAccessMethod parseGeneralName)) n

parseAccessDesc :  Parser (Logging ∘ Dec) AccessDesc
parseAccessDesc = parseTLV _ here' _ parseAccessDescFields

