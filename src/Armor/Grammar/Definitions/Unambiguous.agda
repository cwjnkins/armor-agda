open import Armor.Prelude

module Armor.Grammar.Definitions.Unambiguous (Σ : Set) where

open import Armor.Grammar.Definitions.Unambiguous.Base Σ public

unambiguousHet : ∀ {A : @0 List Σ → Set} → Unambiguous A → UnambiguousHet A
unambiguousHet ua refl a₁ a₂ = ua a₁ a₂
