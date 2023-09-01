{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.Extension.CertPolicy.PolicyInformation
open import Aeres.Data.X509.Extension.CertPolicy.TCB
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.SequenceOf
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Parser
open import Aeres.Prelude

module Aeres.Data.X509.Extension.CertPolicy.Parser where

open Aeres.Grammar.Parser UInt8

private
  here' = "X509: Extension: CertPolicy"

parseCertPolFieldsSeq : Parser (Logging ∘ Dec) CertPolFieldsSeq
parseCertPolFieldsSeq = parseNonEmptySeq "policy info" _ TLV.nonempty TLV.nonnesting parsePolicyInformation

parseCertPolFields : Parser (Logging ∘ Dec) CertPolFields
parseCertPolFields =
  parseTLV _ "cert. policy" _
    (parseExactLength TLV.nonnesting (tell $ here' String.++ ": overflow") parseCertPolFieldsSeq)
