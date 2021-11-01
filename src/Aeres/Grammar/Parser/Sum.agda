{-# OPTIONS --subtyping #-}

open import Aeres.Prelude
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Grammar.Parser.Sum (Σ : Set) where

open import Aeres.Grammar.Definitions Σ
open import Aeres.Grammar.Sum Σ
open import Aeres.Grammar.Parser.Core Σ

module _ {M : Set → Set} ⦃ _ : Monad M ⦄ where
  parseSum : ∀ {A B} → Parser (M ∘ Dec) A → Parser (M ∘ Dec) B → Parser (M ∘ Dec) (Sum A B)
  runParser (parseSum p₁ p₂) xs = do
    no ¬parse₁ ← runParser p₁ xs
      where yes x → return (yes (mapSuccess (λ {xs} x → Sum.inj₁ x) x))
    no ¬parse₂ ← runParser p₂ xs
      where yes x → return (yes (mapSuccess (λ {xs} x → Sum.inj₂ x) x))
    return ∘ no $ λ where
      (success prefix read read≡ (inj₁ x) suffix ps≡) →
        contradiction (success _ _ read≡ x suffix ps≡) ¬parse₁
      (success prefix read read≡ (inj₂ x) suffix ps≡) →
        contradiction (success _ _ read≡ x _ ps≡) ¬parse₂
