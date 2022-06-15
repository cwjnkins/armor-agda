{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X690-DER.Int.TCB
open import Aeres.Data.X690-DER.Tag
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parser
open import Data.List.Properties
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X690-DER.Int.Parser where

open Base256
open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parser      UInt8

module parseInt where
  here' = "parseInt"

  open ≡-Reasoning

  parseIntValue : ∀ n → Parser (Logging ∘ Dec) (ExactLength IntegerValue n)
  runParser (parseIntValue n) xs = do
    yes (success pre₀ r₀ r₀≡ (mk×ₚ (singleton v₀ refl) v₀Len refl) suf₀ ps≡₀)
      ← runParser (parseN n (tell $ here' String.++ ": underflow reading it")) xs
      where no ¬parse → do
        return ∘ no $ λ where
          (success prefix read read≡ (mk×ₚ (mkIntegerValue val bs≡₁) sndₚ refl) suffix ps≡) →
            contradiction
              (success prefix _ read≡
                (mk×ₚ (singleton prefix refl) sndₚ refl)
                suffix ps≡)
              ¬parse
    return (yes
      (success pre₀ _ r₀≡
        (mk×ₚ (mkIntegerValue (twosComplement v₀) refl) v₀Len refl)
        suf₀ ps≡₀))

  parseInt : Parser (Logging ∘ Dec) Int
  parseInt = parseTLV Tag.Integer "Int" IntegerValue parseIntValue

open parseInt public using (parseIntValue ; parseInt)

-- private
--   module Test where

--     intval₁ : List Dig
--     intval₁ = Tag.Integer ∷ # 1 ∷ [ # 255 ]

--     intval₂ : List Dig
--     intval₂ = Tag.Integer ∷ # 2 ∷ # 254 ∷ [ # 255 ]

--     intvalBad : List Dig
--     intvalBad = Tag.Integer ∷ # 4 ∷ # 254 ∷ [ # 255 ]

--     test₁ : Int intval₁
--     test₁ = Success.value (toWitness {Q = Logging.val (runParser parseInt intval₁)} tt)

--     test₂ : Int intval₂
--     test₂ = Success.value (toWitness {Q = Logging.val (runParser parseInt intval₂)} tt)

--     test₃ : ¬ Success _ Int intvalBad
--     test₃ = toWitnessFalse {Q = Logging.val (runParser parseInt intvalBad)} tt
