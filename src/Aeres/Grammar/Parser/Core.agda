{-# OPTIONS --subtyping #-}

open import Aeres.Prelude
open import Data.Nat.Properties
  hiding (_≟_)

module Aeres.Grammar.Parser.Core (Σ : Set) where

open import Aeres.Grammar.Definitions Σ

record Success (A : List Σ → Set) (xs : List Σ) : Set where
  constructor success
  field
    @0 prefix : List Σ
    read   : ℕ
    @0 read≡ : read ≡ length prefix
    value  : A prefix
    suffix : List Σ
    @0 ps≡    : prefix ++ suffix ≡ xs

mapSuccess : ∀ {A B : List Σ → Set} → (∀ {@0 xs} → A xs → B xs) → ∀ {@0 xs} → Success A xs → Success B xs
mapSuccess f (success prefix read read≡ value suffix ps≡ ) = success prefix read read≡ (f value) suffix ps≡

record Parserᵢ (M : List Σ → Set → Set) (A : List Σ → Set) : Set where
  constructor mkParser
  field
    runParser : (xs : List Σ) → M xs (Success A xs)
open Parserᵢ public

Parser : (M : Set → Set) (A : List Σ → Set) → Set
Parser M = Parserᵢ (const M)

module _ {M : Set → Set} ⦃ _ : Monad M ⦄ where

  parseEquivalent : {A B : (@0 _ : List Σ) → Set} → Equivalent A B
                    → Parser (M ∘ Dec) A → Parser (M ∘ Dec) B
  runParser (parseEquivalent equiv p) xs = do
    yes x ← runParser p xs
      where no ¬parse → do
        return ∘ no $ contraposition (mapSuccess (proj₂ equiv)) ¬parse
    return (yes
      (mapSuccess (proj₁ equiv) x))