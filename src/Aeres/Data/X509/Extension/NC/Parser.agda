{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.Extension.NC.GeneralSubtree
open import Aeres.Data.X509.Extension.NC.Properties
open import Aeres.Data.X509.Extension.NC.TCB
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Data.X690-DER.SequenceOf
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
import      Aeres.Grammar.Parallel
import      Aeres.Grammar.Parser
import      Aeres.Grammar.IList
open import Aeres.Prelude

module Aeres.Data.X509.Extension.NC.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8
open Aeres.Grammar.Parallel    UInt8
open Aeres.Grammar.Parser      UInt8
open Aeres.Grammar.IList       UInt8

private
  here' = "X509: Extension: NC"

parseNCFields : Parser (Logging ∘ Dec) NCFields
parseNCFields =
  parseTLV _ here' _
    (parseExactLength TLV.nosubstrings
      (tell $ here' String.++ ": underflow")
      (parseTLV _ here' _ helper))
  where
  helper : (n : ℕ) → Parser (Logging ∘ Dec) (ExactLength (NCFieldsSeqFields) n)
  helper n =  parseEquivalent
      (Parallel.equivalent₁ equivalent)
      (Option.parseOption₂ TLV.nosubstrings TLV.nosubstrings (TLV.noconfusion λ ())
        (parseTLV _ here' _ parseExactLengthGeneralSubtrees)
        (parseTLV _ here' _ parseExactLengthGeneralSubtrees)
        (tell $ here' String.++ ": underflow") n)
