{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Decidable.Int
open import Aeres.Data.X509.Decidable.Length
open import Aeres.Data.X509.Decidable.TLV
open import Aeres.Data.X509.Properties
open import Aeres.Grammar.Definitions
open import Aeres.Grammar.Parser
open import Data.List.Properties
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Decidable.Version where

open Base256

module parseVersion where
  here' = "parseVersion"

  open ≡-Reasoning

  parseVersion : Parser Dig (Logging ∘ Dec) X509.Version
  parseVersion = parseTLV Tag.A0 "version" Generic.Int p
    where
    p : ∀ n → Parser Dig (Logging ∘ Dec) (ExactLength Dig Generic.Int n)
    p = parseExactLength Dig NonNesting.Int (tell $ here' String.++ ": length mismatch") parseInt

open parseVersion public using (parseVersion)
