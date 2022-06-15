{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Decidable.Cert
import      Aeres.Data.X509.Properties as Props
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parser
open import Aeres.Prelude

module Aeres.Data.X509.Completeness where

open Base256
open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parser      UInt8

import Aeres.Grammar.Parser.Completeness UInt8 as ParseComplete

abstract
  parseCert' : Parser (Logging ∘ Dec) X509.Cert
  parseCert' = parseCert

@0 uniqueParse : ParseComplete.UniqueParse X509.Cert
uniqueParse = ParseComplete.uniqueParse (TLV.unambiguous Props.CertFields.unambiguous) TLV.nonnesting

@0 completeParse : ParseComplete.CompleteParse X509.Cert Logging Logging.val parseCert
completeParse =
  ParseComplete.completeParse
    (TLV.unambiguous Props.CertFields.unambiguous) TLV.nonnesting
    {M = Logging} Logging.val parseCert
