{-# OPTIONS --subtyping #-}

open import Aeres.Prelude
open import Data.Nat.Properties
  hiding (_≟_)

module Aeres.Grammar.Properties (Σ : Set) where

open import Aeres.Grammar.Definitions Σ

module Distribute where

open ≡-Reasoning

module _ {@0 A B : @0 List Σ → Set} where

  exactLength-& : ∀ {n} → Equivalent (ExactLength (&ₚ A B) n)
                          (&ₚᵈ (WithinLength A n)
                               (λ bs₁ _ → ExactLength B (n - length bs₁)))
  proj₁ (exactLength-&{n}) (mk×ₚ (mk&ₚ{bs₁ = bs₁}{bs₂} fstₚ₁ sndₚ₂ refl) (─ sndₚ₁) refl) =
    mk&ₚ (mk×ₚ fstₚ₁ (─ subst (length bs₁ ≤_) sndₚ₁ (Lemmas.length-++-≤₁ bs₁ _)) refl)
      (mk×ₚ sndₚ₂ (─ (begin length bs₂ ≡⟨ sym (m+n∸m≡n (length bs₁) _) ⟩
                            length bs₁ + length bs₂ - length bs₁ ≡⟨ cong (_- length bs₁) (sym (length-++ bs₁)) ⟩
                            length (bs₁ ++ bs₂) - length bs₁ ≡⟨ cong (_- length bs₁) sndₚ₁ ⟩
                            n - length bs₁ ∎)) refl)
      refl
  proj₂ (exactLength-&{n}) (mk&ₚ (mk×ₚ{bs = bs₁} fstₚ₁ (─ sndₚ₁) refl) (mk×ₚ{bs = bs₂} fstₚ₂ sndₚ₂ refl) refl) =
    mk×ₚ (mk&ₚ fstₚ₁ fstₚ₂ refl)
      (─ (begin length (bs₁ ++ bs₂) ≡⟨ length-++ bs₁ ⟩
                length bs₁ + length bs₂ ≡⟨ cong (length bs₁ +_) (̂‼ sndₚ₂) ⟩
                length bs₁ + (n - length bs₁) ≡⟨ m+[n∸m]≡n sndₚ₁ ⟩
                n ∎))
      refl
