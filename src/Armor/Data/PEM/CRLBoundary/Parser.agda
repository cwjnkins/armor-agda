{-# OPTIONS --erasure #-}
open import Armor.Data.Base64.TCB
open import Armor.Data.PEM.CRLBoundary.Properties
open import Armor.Data.PEM.CRLBoundary.TCB
open import Armor.Data.PEM.RFC5234
import      Armor.Grammar.Definitions
import      Armor.Grammar.Parser
import      Armor.Grammar.Seq.MaximalParser
open import Armor.Prelude

module Armor.Data.PEM.CRLBoundary.Parser where

open Armor.Grammar.Definitions Char
open Armor.Grammar.Parser      Char
module Seq₁ = Armor.Grammar.Seq.MaximalParser Char

parseCRLBoundary : ∀ ctrl → LogDec.MaximalParser (CRLBoundary ctrl)
parseCRLBoundary ctrl =
  LogDec.equivalent (equiv ctrl)
    (Seq₁.parse&₁
      (parseLitE (tell "parseCRLBoundary: EOF") silent _)
      (λ where _ (─ refl) (─ refl) → refl)
      (LogDec.parseErased parseMaxEOL))
