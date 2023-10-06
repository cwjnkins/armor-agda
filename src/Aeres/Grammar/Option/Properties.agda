{-# OPTIONS --subtyping #-}

import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parallel.TCB
import      Aeres.Grammar.Option.TCB
open import Aeres.Prelude
import      Data.Nat.Properties as Nat
open import Data.Maybe.Properties

module Aeres.Grammar.Option.Properties (Σ : Set) where

open Aeres.Grammar.Definitions  Σ
open Aeres.Grammar.Option.TCB   Σ
open Aeres.Grammar.Parallel.TCB Σ

equivNonEmpty : ∀ {@0 A : @0 List Σ → Set} → @0 NonEmpty A
                → Equivalent (Length≥ (Option A) 1) A
proj₁ (equivNonEmpty ne) (mk×ₚ (some x) sndₚ₁) = x
proj₂ (equivNonEmpty ne) {xs}x =
  mk×ₚ (some x) (─ (Nat.n≢0⇒n>0 (λ x₁ → contradiction (proj₁ (Lemmas.length-++-≡ _ [] _ xs (++-identityʳ xs) x₁)) (ne x))))

instance
  OptionEq≋ : ∀ {@0 A : @0 List Σ → Set} ⦃ _ : Eq≋ A ⦄ → Eq≋ (Option A)
  Eq≋._≋?_ OptionEq≋ {.[]} {.[]} none none = yes ≋-refl
  Eq≋._≋?_ OptionEq≋ {.[]} {bs₂} none (some x) = no (λ where (mk≋ refl ()))
  Eq≋._≋?_ OptionEq≋ {bs₁} {.[]} (some x) none = no λ where (mk≋ refl ())
  Eq≋._≋?_ OptionEq≋ {bs₁} {bs₂} (some v₁) (some v₂) =
    case v₁ ≋? v₂ of λ where
      (yes ≋-refl) → yes ≋-refl
      (no  ¬v₁≋v₂) → no λ where
        ≋-refl → contradiction ≋-refl ¬v₁≋v₂

  OptionEq
    : ∀ {@0 A : @0 List Σ → Set} ⦃ _ : Eq (Exists─ (List Σ) A) ⦄
      → Eq (Exists─ (List Σ) (Option A))
  OptionEq = Eq≋⇒Eq (OptionEq≋ ⦃ Eq⇒Eq≋ it ⦄)

@0 nonmalleable : ∀ {A} → (r : Raw A) → NonMalleable r → NonMalleable (RawOption r) 
nonmalleable r x none none eq = refl
nonmalleable r x (some x₁) (some x₂) eq = case x x₁ x₂ (just-injective eq) ret (const _) of λ where
  refl → refl
