{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Properties as Props
open import Aeres.Grammar.Definitions
open import Aeres.Grammar.Parser
open import Data.List.Properties
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Decidable.INAPFields where

open Base256

module parseINAPFields where
  here' = "parseINAPFields"

  open ≡-Reasoning

  parseINAPFields : Parser Dig (Logging ∘ Dec) X509.INAPFields
  parseINAPFields =
    parseTLV _ " Inhibit Any Policy" _
      λ n → parseExactLength _ TLV.nonnesting (tell $ here' String.++ ": underflow") parseInt n

open parseINAPFields public using (parseINAPFields)
