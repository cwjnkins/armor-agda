{-# OPTIONS --subtyping #-}


open import Aeres.Data.Base64
open import Aeres.Data.PEM.CertText.FullLine.TCB
open import Aeres.Data.PEM.CertText.FullLine.Properties
open import Aeres.Data.PEM.RFC5234
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.IList
import      Aeres.Grammar.Parser
import      Aeres.Grammar.Relation.Definitions
open import Aeres.Prelude

module Aeres.Data.PEM.CertText.FullLine.Parser where

open Aeres.Grammar.Definitions          Char
open Aeres.Grammar.IList                Char
open Aeres.Grammar.Parser               Char
open Aeres.Grammar.Relation.Definitions Char


parseCertFullLine : LogDec.MaximalParser CertFullLine
parseCertFullLine =
  LogDec.equivalent equiv
    (LogDec.parse&₁
      (parseIList (tell "parseCertFullLine: underflow") _
        Base64.Char.nonempty Base64.Char.nonnesting
        parseBase64Char _)
      exactLength-nonnesting
      parseMaxEOL)

