{-# OPTIONS --subtyping #-}

import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option.TCB
open import Aeres.Prelude

module Aeres.Grammar.Option.Properties (Σ : Set) where

open Aeres.Grammar.Definitions Σ
open Aeres.Grammar.Option.TCB  Σ

instance
  OptionEq : ∀ {A : @0 List Σ → Set} ⦃ _ : Eq≋ A ⦄ → Eq≋ (Option A)
  Eq≋._≋?_ OptionEq {.[]} {.[]} none none = yes ≋-refl
  Eq≋._≋?_ OptionEq {.[]} {bs₂} none (some x) = no (λ where (mk≋ refl ()))
  Eq≋._≋?_ OptionEq {bs₁} {.[]} (some x) none = no λ where (mk≋ refl ())
  Eq≋._≋?_ OptionEq {bs₁} {bs₂} (some v₁) (some v₂) =
    case v₁ ≋? v₂ of λ where
      (yes ≋-refl) → yes ≋-refl
      (no  ¬v₁≋v₂) → no λ where
        ≋-refl → contradiction ≋-refl ¬v₁≋v₂
