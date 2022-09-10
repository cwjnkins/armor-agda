{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

module Aeres.Grammar.Relation.Definitions (Σ : Set) where

StrictBoundary : (A B : List Σ → Set) → Set
StrictBoundary A B =
  ∀ xs ys₁ zs₁ ws₁ ys₂ zs₂ ws₂ → xs ≡ ys₁ ++ zs₁ ++ ws₁ → xs ≡ ys₂ ++ zs₂ ++ ws₂
  → A ys₁ → A ys₂ → B zs₁ → B zs₂
  → ys₁ ≡ ys₂

NoOverlap : (A B : List Σ → Set) → Set
NoOverlap A B =
  ∀ ws xs₁ ys₁ xs₂ ys₂ → xs₁ ++ ys₁ ≡ xs₂ ++ ys₂ → A (ws ++ xs₁) → A ws → (xs₁ ≡ []) ⊎ (¬ B xs₂)
