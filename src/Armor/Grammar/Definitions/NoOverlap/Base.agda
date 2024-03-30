open import Armor.Prelude
import      Data.Nat.Properties as Nat

module Armor.Grammar.Definitions.NoOverlap.Base (Σ : Set) where

NoOverlap : (A B : @0 List Σ → Set) → Set
NoOverlap A B =
  ∀ ws xs₁ ys₁ xs₂ ys₂ → xs₁ ++ ys₁ ≡ xs₂ ++ ys₂
  → A (ws ++ xs₁) → A ws → (xs₁ ≡ []) ⊎ (¬ B xs₂)

