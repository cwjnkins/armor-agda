{-# OPTIONS --subtyping #-}

import      Aeres.Grammar.Serializer
import      Aeres.Grammar.Option.Properties
import      Aeres.Grammar.Option.TCB
open import Aeres.Prelude

module Aeres.Grammar.Option (Σ : Set) where

open Aeres.Grammar.Serializer  Σ

open Aeres.Grammar.Option.TCB Σ
  public
  hiding (module Option)

module Option where
  open import Aeres.Grammar.Option.Properties Σ
    public

  serialize : ∀ {@0 A} → Serializer A → Serializer (Option A)
  serialize s none = self
  serialize s (some x) = s x
