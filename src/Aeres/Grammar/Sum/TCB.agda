{-# OPTIONS --subtyping #-}

open import Aeres.Prelude
import      Aeres.Grammar.Definitions.NonMalleable

module Aeres.Grammar.Sum.TCB (Σ : Set) where

open Aeres.Grammar.Definitions.NonMalleable Σ

data Sum (@0 A B : List Σ → Set) (@0 xs : List Σ) : Set where
  inj₁ : A xs → Sum A B xs
  inj₂ : B xs → Sum A B xs

RawSum : {A B : @0 List Σ → Set} → Raw A → Raw B → Raw (Sum A B)
Raw.D (RawSum A B) = (Raw.D A) ⊎ (Raw.D B)
Raw.to (RawSum A B) (fst , inj₁ x) = inj₁ (Raw.to A (fst , x))
Raw.to (RawSum A B) (fst , inj₂ x) = inj₂ (Raw.to B (fst , x))
