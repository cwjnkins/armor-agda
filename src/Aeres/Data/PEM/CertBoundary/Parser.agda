{-# OPTIONS --subtyping #-}


open import Aeres.Data.Base64.TCB
open import Aeres.Data.PEM.CertBoundary.Properties
open import Aeres.Data.PEM.CertBoundary.TCB
open import Aeres.Data.PEM.RFC5234
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parser
open import Aeres.Prelude

module Aeres.Data.PEM.CertBoundary.Parser where

open Aeres.Grammar.Definitions Char
open Aeres.Grammar.Parser      Char

parseCertBoundary : ∀ ctrl → LogDec.MaximalParser (CertBoundary ctrl)
parseCertBoundary ctrl =
  LogDec.equivalent (equiv ctrl)
    (LogDec.parse&₁
      (parseLit (tell "parseCertBoundary: EOF") silent _)
      (λ where _ refl refl → refl)
      (LogDec.parseErased parseMaxEOL))