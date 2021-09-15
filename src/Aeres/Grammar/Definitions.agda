open import Aeres.Prelude

module Aeres.Grammar.Definitions (Σ : Set) where

Unambiguous : (A : List Σ → Set) → Set
Unambiguous A = ∀ {xs} → (a₁ a₂ : A xs) → a₁ ≡ a₂

NonNesting : (A : List Σ → Set) → Set
NonNesting A = ∀ {xs₁ ys₁ xs₂ ys₂} → xs₁ ++ ys₁ ≡ xs₂ ++ ys₂ → A xs₁ → A xs₂ → xs₁ ≡ xs₂

NonEmpty : (A : List Σ → Set) → Set
NonEmpty A = ∀ {xs} → A xs → xs ≢ []


