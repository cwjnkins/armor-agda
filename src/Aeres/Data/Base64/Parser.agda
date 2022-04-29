{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.Base64.TCB
open import Aeres.Data.Base64.Properties
open import Aeres.Prelude
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.IList
import      Aeres.Grammar.Parser

module Aeres.Data.Base64.Parser where

open Base256
open Aeres.Grammar.Definitions Char
open Aeres.Grammar.IList       Char
open Aeres.Grammar.Parser      Char

module parseBase64 where
  hereChar = "parseBase64Char"

  parseBase64Char : Parser (Logging ∘ Dec) Base64Char
  parseBase64Char =
    parseEquivalent Base64Char.equiv
      (parseSigma' {!!} {!!} {!!}
        (parseErased {!!}))
