{-# OPTIONS --subtyping #-}

open import Aeres.Prelude
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Sum
import      Aeres.Grammar.Parser.Core
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Grammar.Parser.Sigma (Σ : Set) where

open Aeres.Grammar.Definitions Σ
open Aeres.Grammar.Sum Σ
open Aeres.Grammar.Parser.Core Σ

module _ {M : Set → Set} ⦃ _ : Monad M ⦄ where
  parseSigma : ∀ {A B}
               → NonNesting A → Unambiguous A
               → Parser (M ∘ Dec) A
               → (∀ {@0 xs} → Decidable (B xs))
               → Parser (M ∘ Dec) (Σₚ A B)
  runParser (parseSigma{B = B} nn ua p d) xs = do
    (yes (success pre₁ r₁ r₁≡ v₁ suf₁ ps≡₁)) ← runParser p xs
      where no ¬parse → do
        return ∘ no $ λ
          x → contradiction
                (mapSuccess (λ { (mk×ₚ z _ refl) → z}) x)
                ¬parse
    case d v₁ ret _ of λ where
      (no ¬p) → do
        return ∘ no $ λ where
          (success prefix read read≡ (mk×ₚ v p refl) suffix ps≡) → ‼
            let @0 pre≡ : prefix ≡ pre₁
                pre≡ = nn (trans₀ ps≡ (sym ps≡₁)) v v₁

                @0 v≡ : subst _ pre≡ v ≡ v₁
                v≡ = ua _ _
            in
            contradiction
              (subst₀ (B pre₁) v≡
                (≡-elim (λ {bs} eq → B bs (subst _ eq v)) p pre≡))
              ¬p
      (yes p) →
        return (yes
          (success pre₁ _ r₁≡ (mk×ₚ v₁ p refl) suf₁ ps≡₁))
