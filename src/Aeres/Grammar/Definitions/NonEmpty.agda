{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

module Aeres.Grammar.Definitions.NonEmpty (Σ : Set) where

NonEmpty : (A : List Σ → Set) → Set
NonEmpty A = ∀ {xs : List Σ} → A xs → xs ≢ []

