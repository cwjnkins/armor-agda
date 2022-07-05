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

module Aeres.Data.X509.Decidable.KUFields where

open Base256

module parseKUFields where
  here' = "parseKUFields"

  open ≡-Reasoning

  parseKUFields : Parser Dig (Logging ∘ Dec) X509.KUFields
  parseKUFields = parseTLV _ "KU Fields" _ (parseExactLength _ TLV.nonnesting (tell $ here' String.++ ": underflow") parseBitstring)

open parseKUFields public using (parseKUFields)


private
  module Test where

    val₁ : List Dig
    val₁ = # 4 ∷ # 4 ∷ # 3 ∷ # 2 ∷ # 5 ∷ [ # 160 ]

    val₂ : List Dig
    val₂ = # 4 ∷ # 4 ∷ # 3 ∷ # 2 ∷ # 4 ∷ [ # 160 ]

    val₃ : List Dig
    val₃ = # 4 ∷ # 4 ∷ # 3 ∷ # 2 ∷ # 6 ∷ [ # 160 ]

    test₁ : X509.KUFields val₁
    test₁ = Success.value (toWitness {Q = Logging.val (runParser parseKUFields val₁)} tt)

    test₂ : X509.KUFields val₂
    test₂ = Success.value (toWitness {Q = Logging.val (runParser parseKUFields val₂)} tt)

    test₃ : ¬ Success _ X509.KUFields val₃
    test₃ = toWitnessFalse {Q = Logging.val (runParser parseKUFields val₃)} tt
