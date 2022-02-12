{-# OPTIONS --subtyping #-}

import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parser.Core
open import Aeres.Prelude

module Aeres.Grammar.Parser.Completeness (Σ : Set) where

open Aeres.Grammar.Definitions Σ
open Aeres.Grammar.Parser.Core Σ

UniqueParse : (List Σ → Set) → Set
UniqueParse A = ∀ {@0 bs} → Unique (Success A bs)

CompleteParse : (A : List Σ → Set) (M : Set → Set)
                → (extract : ∀ {@0 bs} → M (Dec (Success A bs)) → Dec (Success A bs))
                → (parser : Parser (M ∘ Dec) A)
                → Set
CompleteParse A M extract parser =
  ∀ {bs} → (v : Success A bs) → True extract (runParser parser bs) And (v ≡_) 

module _ {@0 A : List Σ → Set} (unambiguousA : Unambiguous A) (nonnestingA : NonNesting A) where

  @0 uniqueParse : UniqueParse A
  uniqueParse p₁ p₂
    with ‼ nonnestingA (trans (Success.ps≡ p₁) (sym (Success.ps≡ p₂))) (Success.value p₁) (Success.value p₂)
  ... | refl
    with ‼ Lemmas.++-cancel≡ˡ (Success.prefix p₁) _ refl (trans (Success.ps≡ p₁) (sym (Success.ps≡ p₂)))
  ... | refl
    with ‼ (trans (Success.read≡ p₁) (sym (Success.read≡ p₂)))
  ... | refl
    with ‼ ≡-unique (Success.read≡ p₂) (Success.read≡ p₁)
    |    ‼ ≡-unique (Success.ps≡ p₂) (Success.ps≡ p₁)
  ... | refl | refl
    with ‼ unambiguousA (Success.value p₁) (Success.value p₂)
  ... | refl = refl

  module _ {M : Set → Set} (extract : ∀ {@0 bs} → M (Dec (Success A bs)) → Dec (Success A bs)) (parser : Parser (M ∘ Dec) A)
    where

    @0 completeParse : CompleteParse A M extract parser
    completeParse{bs} v
      with extract $ runParser parser bs
    ... | (yes v') = uniqueParse v v'
    ... | no ¬v    = contradiction v ¬v
