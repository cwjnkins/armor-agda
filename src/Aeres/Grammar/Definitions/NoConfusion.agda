{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

module Aeres.Grammar.Definitions.NoConfusion (Σ : Set) where

NoConfusion : (A B : List Σ → Set) → Set
NoConfusion A B =
  ∀ {xs₁ ys₁ xs₂ ys₂}
  → (xs₁++ys₁≡xs₂++ys₂ : xs₁ ++ ys₁ ≡ xs₂ ++ ys₂)
  → (a : A xs₁) → ¬ B xs₂

@0 symNoConfusion : ∀ {A B} → NoConfusion A B → NoConfusion B A
symNoConfusion nc ++≡ v₂ v₁ = nc (sym ++≡) v₁ v₂