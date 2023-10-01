{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.TBSCert.Version.TCB
open import Aeres.Data.X690-DER.Int
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parallel
import      Aeres.Grammar.Parser
open import Aeres.Prelude

module Aeres.Data.X509.TBSCert.Version.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parallel    UInt8
open Aeres.Grammar.Parser      UInt8

private
  here' = "X509: TBSCert: Version"

parseVersion : Parser (Logging ∘ Dec) Version
parseVersion = parseTLV Tag.AA0 "version" Int p
  where
  p : ∀ n → Parser (Logging ∘ Dec) (ExactLength Int n)
  p = parseExactLength TLV.nosubstrings (tell $ here' String.++ ": length mismatch") Int.parse
