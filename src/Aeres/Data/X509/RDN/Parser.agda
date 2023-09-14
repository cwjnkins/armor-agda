{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.RDN.ATV
open import Aeres.Data.X509.RDN.Properties
open import Aeres.Data.X509.RDN.TCB
open import Aeres.Data.X690-DER.SequenceOf
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parser
open import Aeres.Prelude

module Aeres.Data.X509.RDN.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parser      UInt8

private
  here' = "X509: RDN"

parse : Parser (Logging ∘ Dec) Name
parse =
  parseSeq here' _ TLV.nonempty TLV.nonnesting
    (parseTLV _ (here' String.++ " (fields)") _
      (λ n → parseBoundedSequenceOf (here' String.++ " (fields)") _ TLV.nonempty TLV.nonnesting ATV.parse n 1 ))
