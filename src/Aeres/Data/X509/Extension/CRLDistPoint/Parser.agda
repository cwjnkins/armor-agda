{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.GeneralNames.TCB
open import Aeres.Data.X509.Extension.CRLDistPoint.DistPoint
open import Aeres.Data.X509.Extension.CRLDistPoint.TCB
open import Aeres.Data.X690-DER.SequenceOf
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Parallel
import      Aeres.Grammar.Parser
open import Aeres.Prelude

module Aeres.Data.X509.Extension.CRLDistPoint.Parser where

open Aeres.Grammar.Parallel UInt8
open Aeres.Grammar.Parser   UInt8

private
  here' = "X509: Extension: CRLDistPoint"

parseCRLDistFields : Parser (Logging ∘ Dec) CRLDistFields
parseCRLDistFields =
  parseTLV _ here' _
    (parseExactLength TLV.nosubstrings (tell $ here' String.++ ": underflow")
      (parseNonEmptySeq (here' String.++ ": elems") _ TLV.nonempty TLV.nosubstrings
        parseDistPoint))
