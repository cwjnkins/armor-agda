{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X690-DER.Int.TCB
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parser
open import Data.List.Properties
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X690-DER.Int.Parser where

open Base256
open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parser      UInt8

module parseInt where
  here' = "parseInt"

  open ≡-Reasoning

  parseIntValue : ∀ n → Parser (Logging ∘ Dec) (ExactLength IntegerValue n)
  parseIntValue = parseExactLengthString (tell $ here' String.++ ": underflow")

  parseInt : Parser (Logging ∘ Dec) Int
  parseInt = parseTLV Tag.Integer "Int" IntegerValue parseIntValue

open parseInt public using (parseIntValue ; parseInt)
