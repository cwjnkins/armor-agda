{-# OPTIONS --subtyping #-}

open import Aeres.Prelude
import      Aeres.Grammar.Serializer
import      Aeres.Grammar.Sum.TCB

module Aeres.Grammar.Sum.Serializer (Σ : Set) where

open Aeres.Grammar.Sum.TCB    Σ
open Aeres.Grammar.Serializer Σ

serialize : ∀ {@0 A B}
            → Serializer A → Serializer B
            → Serializer (Sum A B)
serialize sa sb (inj₁ x) = sa x
serialize sa sb (inj₂ x) = sb x
