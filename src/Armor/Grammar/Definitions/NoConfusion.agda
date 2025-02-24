{-# OPTIONS --erasure #-}
open import Armor.Prelude

module Armor.Grammar.Definitions.NoConfusion (Σ : Set) where

open import Armor.Grammar.Definitions.NoConfusion.Base Σ public

@0 symNoConfusion : ∀ {A B} → NoConfusion A B → NoConfusion B A
symNoConfusion nc ++≡ v₂ v₁ = nc (sym ++≡) v₁ v₂
