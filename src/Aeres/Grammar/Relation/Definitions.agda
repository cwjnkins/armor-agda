{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

module Aeres.Grammar.Relation.Definitions (Σ : Set) where

StrictBounday : (A B : List Σ → Set) → Set
StrictBounday A B =
  ∀ xs ys₁ zs₁ ys₂ zs₂ → xs ≡ ys₁ ++ zs₁ → xs ≡ ys₂ ++ zs₂
  → A ys₁ → A ys₂ → B zs₁
  → ys₁ ≡ ys₂
