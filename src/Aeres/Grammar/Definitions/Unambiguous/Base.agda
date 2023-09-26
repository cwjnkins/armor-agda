{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

module Aeres.Grammar.Definitions.Unambiguous.Base (Σ : Set) where

-- `A` is unambiguous iff there is only one way for a given string to be
-- accepted by the grammar

Unambiguous : (A : List Σ → Set) → Set
Unambiguous A = ∀ {xs} → (a₁ a₂ : A xs) → a₁ ≡ a₂

