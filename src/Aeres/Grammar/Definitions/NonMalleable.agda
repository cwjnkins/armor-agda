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

record Raw₁ {A : @0 List Σ → Set} (R : Raw A) (P : {@0 xs : List Σ} → A xs → @0 List Σ → Set) : Set₁ where
  field
    D : Raw.D R → Set
    to : ∀ {@0 bs} → (a : A bs) → Exists─ (List Σ) (P a) → D (Raw.to R (─ _ , a))

record NonMalleable (A : @0 List Σ → Set) (R : Raw A) : Set where
  open Raw R public
  field
    unambiguous : Unambiguous A
    injective : ∀ a₁ a₂ → to a₁ ≡ to a₂ → a₁ ≡ a₂

record NonMalleable₁
  {A : @0 List Σ → Set} {R : Raw A}
  (P : {@0 xs : List Σ} → A xs → @0 List Σ → Set) (RP : Raw₁ R P) : Set where
  open Raw₁ RP public
  field
    unambiguous : ∀ {@0 xs} → (a : A xs) → Unambiguous (P a)
    injective   : ∀ {@0 bs} a p₁ p₂ → to{bs} a p₁ ≡ to{bs} a p₂ → p₁ ≡ p₂
