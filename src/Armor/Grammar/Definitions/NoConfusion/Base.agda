{-# OPTIONS --erasure #-}
open import Armor.Prelude

module Armor.Grammar.Definitions.NoConfusion.Base (Σ : Set) where

NoConfusion : (A B : @0 List Σ → Set) → Set
NoConfusion A B =
  ∀ {xs₁ ys₁ xs₂ ys₂}
  → (xs₁++ys₁≡xs₂++ys₂ : xs₁ ++ ys₁ ≡ xs₂ ++ ys₂)
  → (a : A xs₁) → ¬ B xs₂
