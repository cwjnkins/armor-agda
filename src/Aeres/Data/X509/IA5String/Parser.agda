{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.IA5String.TCB
open import Aeres.Data.X690-DER
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parser
open import Aeres.Prelude

module Aeres.Data.X509.IA5String.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parser      UInt8

parseIA5StringValue : ∀ n → Parser (Logging ∘ Dec) (ExactLength IA5StringValue n)
runParser (parseIA5StringValue n) xs = do
  yes (success pre₀ r₀ r₀≡ (mk×ₚ (singleton os₀ refl) (─ osLen) refl) suf₀ ps≡₀) ← runParser (parseOctetStringValue n) xs
    where no ¬parse → do
      return ∘ no $ λ where
        (success prefix read read≡ (mk×ₚ (mkIA5StringValue str all<128) strLen refl) suffix ps≡) →
          contradiction
            (success prefix _ read≡
              (mk×ₚ str strLen refl) _ ps≡)
            ¬parse
  case All.all? (Fin._<? (# 128)) os₀ of λ where
    (no  all≮128) → do
      tell $ here' String.++ ": value violation"
      return ∘ no $ λ where
        (success .str' _ read≡ (mk×ₚ (mkIA5StringValue (singleton str' refl) all<128) (─ strLen) refl) suffix ps≡) → ‼
          let @0 pre₀≡ : pre₀ ≡ str'
              pre₀≡ = proj₁ $
                Lemmas.length-++-≡ _ suf₀ _ suffix
                  (trans ps≡₀ (sym ps≡))
                  (trans osLen (sym strLen))
          in
          contradiction (subst (All _) (sym pre₀≡) all<128) all≮128
    (yes all<128) →
      return (yes
        (success pre₀ _ r₀≡
          (mk×ₚ (mkIA5StringValue (singleton os₀ refl) all<128) (─ osLen) refl)
          suf₀ ps≡₀))
  where here' = "parseIA5StringValue"

parseIA5String : Parser (Logging ∘ Dec) IA5String
parseIA5String = parseTLV _ "IA5String" _ parseIA5StringValue

parsePrintableString : Parser (Logging ∘ Dec) PrintableString
parsePrintableString =
  parseTLV Tag.PrintableString "printable string" IA5StringValue parseIA5StringValue
