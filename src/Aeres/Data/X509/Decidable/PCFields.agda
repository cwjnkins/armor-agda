{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Decidable.GeneralName
open import Aeres.Data.X509.Decidable.Int
open import Aeres.Data.X509.Decidable.Length
open import Aeres.Data.X509.Decidable.SequenceOf
open import Aeres.Data.X509.Decidable.TLV
open import Aeres.Data.X509.Properties as Props
open import Aeres.Grammar.Definitions
open import Aeres.Grammar.Parser
open import Data.List.Properties
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Decidable.PCFields where

open Base256

module parsePCFields where
  here' = "parsePCFields"

  open ≡-Reasoning

  parsePCFields : Parser Dig (Logging ∘ Dec) X509.PCFields
  parsePCFields =
    parseTLV _ "Policy Constraiint Fields" _
      (parseExactLength _ Props.TLV.nonnesting (tell $ here' String.++ ": underflow")
        (parseTLV _ "Policy Constraiint Fields" _ helper))
    where
    helper : (n : ℕ) → Parser Dig (Logging ∘ Dec) (ExactLength Dig (X509.PCFieldsSeqFields) n)
    helper n =
      parseEquivalent _ (equivalent×ₚ _ Props.PCFieldsSeqFields.equivalent)
        (parseOption₂ _ Props.TLV.nonnesting Props.TLV.nonnesting (TLV.noconfusion (λ ()))
          (parseTLV _ "require explicit policy" _ parseIntValue)
          (parseTLV _ "inhibit policy mapping" _ parseIntValue)
          (tell $ here' String.++ ": underflow") n)

open parsePCFields public using (parsePCFields)
