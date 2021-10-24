{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Decidable.Length
open import Aeres.Data.X509.Decidable.TLV
open import Aeres.Data.X509.Properties
open import Aeres.Grammar.Definitions
open import Aeres.Grammar.Parser
open import Data.List.Properties
open import Data.Nat.Properties
  hiding (_≟_)

module Aeres.Data.X509.Decidable.SignAlg where

open Base256

postulate
  parseSignAlgFields : ∀ n → Parser Dig (Logging ∘ Dec) (ExactLength _ X509.SignAlgFields n)

parseSignAlg : Parser Dig (Logging ∘ Dec) X509.SignAlg
parseSignAlg =
  parseTLV _ "signature algorithm" _ parseSignAlgFields

-- tests are needed to be run after writing the parser
private
  module Test where

    Sa₁ : List Dig
    Sa₁ = Tag.Sequence ∷ # 13 ∷ # 6 ∷ # 9 ∷ # 42 ∷ # 134 ∷ # 72 ∷ # 134 ∷ # 247 ∷ # 13 ∷ # 1 ∷ # 1 ∷ # 1 ∷ # 5 ∷ [ # 0 ]

    Sa₂ : List Dig
    Sa₂ = Tag.Sequence ∷ # 11 ∷ # 6 ∷ # 9 ∷ # 42 ∷ # 134 ∷ # 72 ∷ # 134 ∷ # 247 ∷ # 13 ∷ # 1 ∷ # 1 ∷ [ # 1 ]

    Sa₃ : List Dig
    Sa₃ = Tag.Sequence ∷ # 13 ∷ # 6 ∷ # 9 ∷ # 42 ∷ # 134 ∷ # 72 ∷ # 134 ∷ # 247 ∷ # 13 ∷ # 1 ∷ # 1 ∷ # 11 ∷ # 5 ∷ [ # 0 ]

    -- satest₁ : X509.SignAlg Sa₁
    -- satest₁ = Success.value (toWitness {Q = Logging.val (runParser parseSignAlg Sa₁)} tt)

    -- satest₂ : X509.SignAlg Sa₂
    -- satest₂ = Success.value (toWitness {Q = Logging.val (runParser parseSignAlg Sa₂)} tt)

    -- satest₃ : X509.SignAlg Sa₃
    -- satest₃ = Success.value (toWitness {Q = Logging.val (runParser parseSignAlg Sa₃)} tt)

