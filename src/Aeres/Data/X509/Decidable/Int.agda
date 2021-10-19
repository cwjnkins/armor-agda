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
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Decidable.Int where

open Base256

module parseInt where
  here' = "parseInt"

  open ≡-Reasoning

  parseIntValue : ∀ n → Parser Dig (Logging ∘ Dec) (ExactLength Dig Generic.IntegerValue n)
  runParser (parseIntValue n) xs = do
    yes (success pre₀ r₀ r₀≡ (mk×ₚ (singleton v₀ refl) v₀Len refl) suf₀ ps≡₀)
      ← runParser (parseN Dig n (tell $ here' String.++ ": underflow reading it")) xs
      where no ¬parse → do
        return ∘ no $ λ where
          (success prefix read read≡ (mk×ₚ (Generic.mkIntegerValue val bs≡₁) sndₚ refl) suffix ps≡) →
            contradiction
              (success prefix _ read≡
                (mk×ₚ (singleton prefix refl) sndₚ refl)
                suffix ps≡)
              ¬parse
    return (yes
      (success pre₀ _ r₀≡
        (mk×ₚ (Generic.mkIntegerValue (twosComplement v₀) refl) v₀Len refl)
        suf₀ ps≡₀))

  parseInt : Parser Dig (Logging ∘ Dec) Generic.Int
  parseInt = parseTLV Tag.Integer "Int" Generic.IntegerValue parseIntValue

open parseInt public using (parseIntValue ; parseInt)


private
  module Test where

    intval₁ : List Dig
    intval₁ = Tag.Integer ∷ # 1 ∷ [ # 255 ]

    intval₂ : List Dig
    intval₂ = Tag.Integer ∷ # 2 ∷ # 254 ∷ [ # 255 ]

    intvalBad : List Dig
    intvalBad = Tag.Integer ∷ # 4 ∷ # 254 ∷ [ # 255 ]

    test₁ : Generic.Int intval₁
    test₁ = Success.value (toWitness {Q = Logging.val (runParser parseInt intval₁)} tt)

    test₂ : Generic.Int intval₂
    test₂ = Success.value (toWitness {Q = Logging.val (runParser parseInt intval₂)} tt)

    test₃ : ¬ Success _ Generic.Int intvalBad
    test₃ = toWitnessFalse {Q = Logging.val (runParser parseInt intvalBad)} tt
