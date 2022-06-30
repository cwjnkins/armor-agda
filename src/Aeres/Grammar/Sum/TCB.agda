{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

module Aeres.Grammar.Sum.TCB (Σ : Set) where

data Sum (@0 A B : List Σ → Set) (@0 xs : List Σ) : Set where
  inj₁ : A xs → Sum A B xs
  inj₂ : B xs → Sum A B xs

