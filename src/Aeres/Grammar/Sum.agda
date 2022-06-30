{-# OPTIONS --subtyping #-}

open import Aeres.Prelude
import      Aeres.Grammar.Sum.Properties
import      Aeres.Grammar.Sum.Serializer
import      Aeres.Grammar.Sum.TCB

module Aeres.Grammar.Sum (Σ : Set) where

-- TODO: have these be qualified names ("Sum.nonempty")
open Aeres.Grammar.Sum.Properties Σ
  public
  renaming ( nonempty     to nonemptySum
           ; nonnesting   to nonnestingSum
           ; unambiguous' to unambiguousSum'
           ; unambiguous  to unambiguousSum)
open Aeres.Grammar.Sum.TCB        Σ public
  hiding (module Sum)

module Sum where
  open Aeres.Grammar.Sum.Serializer Σ public
  open Aeres.Grammar.Sum.TCB        Σ public
    using (inj₁ ; inj₂)
