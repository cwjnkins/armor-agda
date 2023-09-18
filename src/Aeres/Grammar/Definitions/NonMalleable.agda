{-# OPTIONS --subtyping #-}

import      Aeres.Grammar.Definitions
  using (Unambiguous)
open import Aeres.Prelude
  renaming (Σ to Sigma)

module Aeres.Grammar.Definitions.NonMalleable (Σ : Set) where

open Aeres.Grammar.Definitions Σ

record Raw (A : @0 List Σ → Set) : Set₁ where
  field
    D : Set
    to : Exists─ (List Σ) A → D

record NonMalleable (A : @0 List Σ → Set) (R : Raw A) : Set where
  open Raw R public
  field
    unambiguous : Unambiguous A
    injective : ∀ a₁ a₂ → to a₁ ≡ to a₂ → a₁ ≡ a₂
