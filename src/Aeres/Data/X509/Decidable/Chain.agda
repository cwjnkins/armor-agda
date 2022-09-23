{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.IList
import      Aeres.Grammar.Parser
import      Aeres.Grammar.Parser.Maximal
import      Aeres.Grammar.Properties
open import Aeres.Data.X509
open import Aeres.Data.X509.Decidable.Cert
open import Aeres.Data.X509.Properties as Props

module Aeres.Data.X509.Decidable.Chain where

open Base256
open Aeres.Grammar.Definitions    UInt8
open Aeres.Grammar.IList          UInt8
open Aeres.Grammar.Parser         UInt8
open Aeres.Grammar.Parser.Maximal UInt8
open Aeres.Grammar.Properties     UInt8

module parseChain where

  here' = "parseChain"

  parseChain : Parser (Logging ∘ Dec) X509.Chain
  parseChain =
    LogDec.MaximalParser.parser
      (parseIListMax.parseIListLowerBounded
        (mkLogged ["parseChain: underflow"] tt)
        _ TLV.nonempty TLV.nonnesting parseCert _)

open parseChain public using (parseChain)
