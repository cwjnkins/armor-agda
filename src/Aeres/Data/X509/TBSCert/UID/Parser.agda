{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.TBSCert.UID.TCB
open import Aeres.Data.X690-DER.BitString
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Parser
open import Aeres.Prelude

module Aeres.Data.X509.TBSCert.UID.Parser where

open Aeres.Grammar.Parser UInt8

private
  here' = "X509: TBSCert: UID"

parseIssUID : Parser (Logging ∘ Dec) IssUID
parseIssUID =
  parseTLV Tag.A81 (here' String.++ ": issuer") BitStringValue parseBitstringValue

parseSubUID : Parser (Logging ∘ Dec) SubUID
parseSubUID =
  parseTLV Tag.A82 (here' String.++ ": subject") BitStringValue parseBitstringValue
