{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Decidable.Boool
open import Aeres.Data.X509.Decidable.Int
open import Aeres.Data.X509.Decidable.Length
open import Aeres.Data.X509.Decidable.Octetstring
open import Aeres.Data.X509.Decidable.Seq
open import Aeres.Data.X509.Decidable.TLV
open import Aeres.Data.X509.Properties as Props
open import Aeres.Grammar.Definitions
open import Aeres.Grammar.Parser
open import Data.List.Properties
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Decidable.BCFields where

open Base256

module parseBCFields where
  here' = "parseBCFields"

  open ≡-Reasoning


  parseBCFieldsSeqFields : ∀ n → Parser Dig (Logging ∘ Dec) (ExactLength _ X509.BCFieldsSeqFields n)
  parseBCFieldsSeqFields n =
    parseEquivalent _ (equivalent×ₚ _ Props.BCFieldsSeqFields.equivalent)
      (parseOption₂ _ Props.TLV.nonnesting Props.TLV.nonnesting (TLV.noconfusion λ where ()) parseBool parseInt (tell $ here' String.++ ": underflow") _)

  parseBCFieldsSeq : Parser Dig (Logging ∘ Dec) X509.BCFieldsSeq
  parseBCFieldsSeq = parseTLV _ "BC Fields Seq" _ parseBCFieldsSeqFields

  parseBCFields : Parser Dig (Logging ∘ Dec) X509.BCFields
  parseBCFields = parseTLV _ "BC Fields" _ (parseExactLength _ Props.TLV.nonnesting (tell $ here' String.++ ": underflow") parseBCFieldsSeq)