{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

module Aeres.Grammar.Relation.Definitions (Σ : Set) where

NoOverlap : (A B : List Σ → Set) → Set
NoOverlap A B =
  ∀ ws xs₁ ys₁ xs₂ ys₂ → xs₁ ++ ys₁ ≡ xs₂ ++ ys₂
  → A (ws ++ xs₁) → A ws → (xs₁ ≡ []) ⊎ (¬ B xs₂)
