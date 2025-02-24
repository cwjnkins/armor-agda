{-# OPTIONS --erasure #-}
open import Armor.Prelude
  renaming (Σ to Sigma)

module Armor.Grammar.Definitions.Eq.Base (Σ : Set) where

infix 4 _≋_
record _≋_ {A : @0 List Σ → Set} {@0 bs₁ bs₂} (a₁ : A bs₁) (a₂ : A bs₂) : Set where
  constructor mk≋
  field
    @0 bs≡ : bs₁ ≡ bs₂
    @0 a≡  : subst₀! A bs≡ a₁ ≡ a₂

pattern ≋-refl = mk≋ refl refl

Decidable-≋ : (@0 List Σ → Set) → Set
Decidable-≋ A = ∀ {@0 bs₁ bs₂} (a₁ : A bs₁) (a₂ : A bs₂) → Dec (_≋_{A} a₁ a₂)

record Eq≋ (@0 A : @0 List Σ → Set) : Set where
  infix 4 _≋?_
  field
    _≋?_ : Decidable-≋ A

open Eq≋ ⦃ ... ⦄ public

