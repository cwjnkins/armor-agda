{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

module Aeres.Grammar.Serializer (Σ : Set) where

Serializer : (A : @0 List Σ → Set) → Set
Serializer A = ∀ {@0 bs} → A bs → Singleton bs
