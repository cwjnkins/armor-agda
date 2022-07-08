{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.Base64.TCB
open import Aeres.Data.Base64.Properties
open import Aeres.Prelude
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.IList
import      Aeres.Grammar.Parser
import      Aeres.Grammar.Properties

module Aeres.Data.Base64.Parser where

open Base256
open Aeres.Grammar.Definitions Char
open Aeres.Grammar.IList       Char
open Aeres.Grammar.Parser      Char
module Props = Aeres.Grammar.Properties Char

module parseBase64 where
  hereChar = "parseBase64Char"

  open ≡-Reasoning

  parseBase64Char : Parser (Logging ∘ Dec) Base64Char
  parseBase64Char =
    parseEquivalent Base64Char.equiv
      (parseSigma' (Props.NonNesting.erased exactLength-nonnesting)
        (λ where
          {c ∷ []} (─ e@(mk×ₚ self (─ refl) refl)) →
            case c ∈? Base64.charset of λ where
              (no ¬c∈) →
                no λ where
                  (─ c∈ , snd) → contradiction c∈ ¬c∈
              (yes c∈) → yes ((─ c∈) , self))
          (λ where
            {bs} (─ mk×ₚ self (─ len≡) refl) (─ mk×ₚ self (─ len≡') refl) (─ c∈ , singleton i i≡) →
              let @0 c : Char
                  c = lookupELS{bs} (mk×ₚ self (─ len≡) refl) (# 0)
                  bs≡ : Erased (bs ≡ [ c ])
                  bs≡ = ─ (case ((Σ[ xs ∈ List Char ] length xs ≡ 1) ∋ bs , len≡) ret (λ where (bs' , bsLen) → bs' ≡ [ lookupELS (mkELS 1 bs' bsLen) (# 0) ]) of λ where
                            (c ∷ [] , refl) → refl)
              in
              subst₀
                (λ xs → (@0 len≡“ : length xs ≡ 1) →
                  Exists─ (lookupELS (mkELS 1 xs len≡“) (# 0) ∈ Base64.charset)
                    λ (@0 c∈₁) → Singleton (Any.index c∈₁))
                (sym $ Erased.x bs≡)
                  (λ where refl → (─ c∈) , (singleton i i≡))
                  len≡')
        (parseErased (parseExactLengthString (tell $ hereChar String.++ ": underflow") 1)))

  parseBase64Str : ∀ n {n%4 : True (n % 4 ≟ 0)}  → Parser (Logging ∘ Dec) (ExactLength Base64Str n)
  runParser (parseBase64Str n {n%4}) xs = do
    yes (success .v₀ r₀ r₀≡ (mk×ₚ (singleton v₀ refl) (─ v₀Len) refl) suf₀ ps≡₀)
      ← runParser (parseExactLengthString (tell $ "parseBase64Str: underflow") n) xs
      where no ¬parse → do
        return ∘ no $ λ where
          (success prefix read read≡ (mk×ₚ str (─ strLen) bs≡) suffix ps≡) →
            contradiction (success prefix _ read≡ (mk×ₚ self (─ strLen) bs≡) suffix ps≡) ¬parse
    case Base64Str.b64Str? v₀ of λ where
      (no ¬p) → return ∘ no $ λ where
        (success prefix read read≡ (mk×ₚ{bs} str (─ strLen) refl) suffix ps≡) →
          contradiction
            (subst Base64Str
              (proj₁
                (Lemmas.length-++-≡ _ _ _ _
                  (begin (prefix ++ suffix ≡⟨ ps≡ ⟩
                         xs                ≡⟨ sym ps≡₀ ⟩
                         v₀ ++ suf₀        ∎))
                  (begin length bs ≡⟨ strLen ⟩
                         n         ≡⟨ sym v₀Len ⟩
                         length v₀ ∎)))
              str)
            ¬p
      (yes p) → return (yes (success v₀ r₀ r₀≡ (mk×ₚ p (─ v₀Len) refl) suf₀ ps≡₀))
