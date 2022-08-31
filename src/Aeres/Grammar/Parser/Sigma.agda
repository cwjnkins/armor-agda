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
  parseSigma'
    : ∀ {@0 A B}
      → @0 NonNesting A
      → (∀ {xs} → Decidable (B xs))
      → (∀ {@0 xs} → (a₁ a₂ : A xs) → B _ a₁ → B _ a₂)
      → Parser (M ∘ Dec) A
      → Parser (M ∘ Dec) (Σₚ A B)
  runParser (parseSigma'{A}{B} nn d i p) xs = do
    (yes (success pre₁ r₁ r₁≡ v₁ suf₁ ps≡₁)) ← runParser p xs
      where no ¬parse → do
        return ∘ no $ λ
          x → contradiction
                (mapSuccess (λ { (mk×ₚ z _ refl) → z}) x)
                ¬parse
    let pre₁' = take r₁ xs
    let pre₁≡ : Erased (pre₁ ≡ pre₁')
        pre₁≡ = ─ subst (λ x → pre₁ ≡ take x xs) (sym r₁≡)
                    (subst (λ x → pre₁ ≡ take (length pre₁) x) ps≡₁
                      (sym (Lemmas.take-length-++ pre₁ _)))
    case d {pre₁'} (subst₀ A (Erased.x pre₁≡) v₁) ret _ of λ where
      (no ¬p) →
        return ∘ no $ λ where
          (success prefix read read≡ (mk×ₚ v p refl) suffix ps≡) → ‼
            let @0 pre≡ : prefix ≡ take r₁ xs
                pre≡ = trans (nn (trans₀ ps≡ (sym ps≡₁)) v v₁) (Erased.x pre₁≡)

                v₁' = (subst₀ A (Erased.x pre₁≡) v₁)

                p' : B pre₁' v₁'
                p' = i (subst A pre≡ v) v₁'
                       (≡-elim (λ {p} eq → B p (subst A eq v)) p pre≡)
            in
            contradiction p' ¬p
      (yes p) →
        return (yes
          (success pre₁ _ r₁≡ (mk×ₚ (subst₀ A (Erased.x pre₁≡) v₁) p (sym (Erased.x pre₁≡))) _ ps≡₁))

  parseSigma
    : ∀ {A B}
      → @0 NonNesting A → @0 Unambiguous A
      → Parser (M ∘ Dec) A
      → (∀ {@0 xs} → Decidable (B xs))
      → Parser (M ∘ Dec) (Σₚ A B)
  parseSigma{B = B} nn ua p d = parseSigma' nn d (λ {xs} a₁ a₂ b → subst₀ (B xs) (ua a₁ a₂) b) p
