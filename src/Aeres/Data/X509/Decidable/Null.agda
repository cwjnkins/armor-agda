{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Decidable.TLV
open import Aeres.Grammar.Definitions
open import Aeres.Grammar.Parser

module Aeres.Data.X509.Decidable.Null where

open Base256

module parseNull where
  here' = "parseNull"

  open ≡-Reasoning

  parseNull : Parser Dig (Logging ∘ Dec) Null
  parseNull =
    (parseTLV Tag.Null "null" (_≡ [])
      (parseExactLength _ (λ where _ refl refl → refl) (tell $ here' String.++ ": nonzero length")
        (parseLit _ (return (Level.lift tt)) (return (Level.lift tt)) [])))

open parseNull public using (parseNull)

private
  module Test where

    Null₁ : List Dig
    Null₁ = Tag.Null ∷ [ # 0 ]

    Badnull₂ : List Dig
    Badnull₂ = Tag.Null ∷ # 1 ∷ [ # 0 ]

    test₁ : Null Null₁
    test₁ = Success.value (toWitness {Q = Logging.val (runParser parseNull Null₁)} tt)

    test₂ : ¬ Success _ Null Badnull₂
    test₂ = toWitnessFalse {Q = Logging.val (runParser parseNull Badnull₂)} tt
