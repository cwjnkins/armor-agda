{-# OPTIONS --subtyping #-}

import      Armor.Grammar.DSum.TCB
import      Armor.Grammar.Definitions
open import Armor.Prelude

module Armor.Grammar.DSum.Properties (Σ : Set) where

open Armor.Grammar.DSum.TCB    Σ
open Armor.Grammar.Definitions Σ

@0 nonnesting
  : {n : ℕ} {A : Vec Σ n → Set} {B : ∀ {xs} → A xs → List Σ → Set}
    → (∀ {xs} → Unique (A xs))
    → (∀ {xs} → (d : A xs) → NonNesting (B d))
    → NonNesting (DSum A B)
nonnesting ua nn xs₁++ys₁≡xs₂++ys₂ (mkDSum{look} discr value look≡) (mkDSum{look₁} discr₁ value₁ look≡₁) = {!!}
  where
  @0 look≡look₁ : look ≡ look₁
  look≡look₁ = {!!}
