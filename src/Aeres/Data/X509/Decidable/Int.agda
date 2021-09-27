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

  parseInt : Parser Dig (Logging ∘ Dec) Generic.Int
  parseInt = parseTLV Tag.Integer "Int" Generic.IntegerValue p
    where
    p : ∀ n → Parser Dig (Logging ∘ Dec) (ExactLength Dig Generic.IntegerValue n)
    runParser (p n) xs = do
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

open parseInt public using (parseInt)
