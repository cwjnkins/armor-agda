{-# OPTIONS --subtyping #-}

import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Serializer
open import Aeres.Prelude

module Aeres.Grammar.Option (Σ : Set) where

open Aeres.Grammar.Definitions Σ
open Aeres.Grammar.Serializer  Σ

serialize : ∀ {@0 A} → Serializer A → Serializer (Option A)
serialize s none = self
serialize s (some x) = s x
