{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.Strings.PrintableString.Char
open import Aeres.Data.X690-DER.Strings.PrintableString.TCB
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.IList
import      Aeres.Grammar.Parallel
import      Aeres.Grammar.Parser
open import Aeres.Prelude

module Aeres.Data.X690-DER.Strings.PrintableString.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.IList       UInt8
open Aeres.Grammar.Parallel    UInt8
open Aeres.Grammar.Parser      UInt8

private
  here' = "X690-DER: Strings: PrintableString: "

  parseExact : ∀ n → Parser (Logging ∘ Dec) (ExactLength (IList PrintableStringChar) n)
  parseExact n =
    parseIList
      (tell $ here' String.++ "parseExact: underflow")
      _ Char.nonempty Char.nosubstrings Char.parse _

parsePrintableString : Parser (Logging ∘ Dec) PrintableString
parsePrintableString = parseTLV _ here' _ parseExact
