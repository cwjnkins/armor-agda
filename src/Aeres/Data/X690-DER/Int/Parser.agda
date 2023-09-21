{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X690-DER.Int.TCB
import      Aeres.Data.X690-DER.Tag as Tag
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

private
  here' = "X690-DER: Int"

parseValue : ∀ n → Parser (Logging ∘ Dec) (ExactLength IntegerValue n)
runParser (parseValue zero) xs = do
  tell $ here' String.++ " (value): cannot read 0-length integer"
  return ∘ no $ λ where
    (success prefix read read≡ (mk×ₚ (mkIntVal bₕ bₜ minRep val refl) (─ ()) refl) suffix ps≡)
runParser (parseValue (suc n)) xs = do
  (yes (success ._ r@._ refl (mk×ₚ (singleton (v₁₁ ∷ v₁) refl) (─ v₁Len) refl) suf₁ refl))
    ← runParser (parseExactLengthString (tell $ here' String.++ ": underflow reading " String.++ show (suc n) String.++ " bytes") (suc n)) xs
    where no ¬p → do
      return ∘ no $ λ where
        (success prefix read read≡ (mk×ₚ _ (─ vLen) refl) suffix ps≡) →
          contradiction
            (success prefix _ read≡ (mk×ₚ self (─ vLen) refl) suffix ps≡)
            ¬p
  case twosComplementMinRep? v₁₁ v₁ ret (const _) of λ where
    (no ¬p) → do
      tell $ here' String.++ " (value): bytestring is not minimum representation: " String.++ show (map Fin.toℕ (v₁₁ ∷ v₁))
      return ∘ no $ λ where
        (success prefix read read≡ (mk×ₚ (mkIntVal bₕ bₜ minRep (singleton v v≡) refl) (─ vLen) refl) suffix ps≡) →
          let
            bₕ∷bₜ≡v₁₁∷v₁ : Erased (_≡_{A = List UInt8} (bₕ ∷ bₜ) (v₁₁ ∷ v₁))
            bₕ∷bₜ≡v₁₁∷v₁ =
              ─ proj₁ (Lemmas.length-++-≡ _ suffix _ suf₁
                         ps≡ (trans vLen (sym v₁Len)))
          in
          contradiction
            (subst₂ UInt8.TwosComplementMinRep (∷-injectiveˡ (¡ bₕ∷bₜ≡v₁₁∷v₁)) (∷-injectiveʳ (¡ bₕ∷bₜ≡v₁₁∷v₁)) (toWitness minRep))
            ¬p
    (yes mr) →
      return (yes
        (success (v₁₁ ∷ v₁) r refl (mk×ₚ (mkIntVal v₁₁ v₁ (fromWitness mr) self refl) (─ v₁Len) refl) suf₁ refl))

parse : Parser (Logging ∘ Dec) Int
parse = parseTLV Tag.Integer here' _ parseValue
