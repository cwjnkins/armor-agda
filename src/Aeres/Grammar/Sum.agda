{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

module Aeres.Grammar.Sum (Σ : Set) where

open import Aeres.Grammar.Definitions Σ

data Sum (A B : (List Σ) → Set) : (@0 _ : List Σ) → Set where
  inj₁ : ∀ {@0 xs} → A xs → Sum A B xs
  inj₂ : ∀ {@0 xs} → B xs → Sum A B xs

nonnestingSum : ∀ {A B} → NonNesting A → NonNesting B → NoConfusion A B → NonNesting (Sum A B)
nonnestingSum nn₁ nn₂ nc ++≡ (inj₁ x) (inj₁ x₁) = nn₁ ++≡ x x₁
nonnestingSum nn₁ nn₂ nc ++≡ (inj₁ x) (inj₂ x₁) = ⊥-elim (nc ++≡ x x₁)
nonnestingSum nn₁ nn₂ nc ++≡ (inj₂ x) (inj₁ x₁) = ⊥-elim (nc (sym ++≡) x₁ x)
nonnestingSum nn₁ nn₂ nc ++≡ (inj₂ x) (inj₂ x₁) = nn₂ ++≡ x x₁
