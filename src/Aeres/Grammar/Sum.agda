open import Aeres.Prelude
import      Aeres.Grammar.Sum.Parser
import      Aeres.Grammar.Sum.Properties
import      Aeres.Grammar.Sum.Serializer
import      Aeres.Grammar.Sum.TCB

module Aeres.Grammar.Sum (Σ : Set) where

open Aeres.Grammar.Sum.TCB    Σ public
  hiding (module Sum)
open Aeres.Grammar.Sum.Parser Σ public

module Sum where
  open Aeres.Grammar.Sum.Properties Σ public
  open Aeres.Grammar.Sum.Serializer Σ public
  open Aeres.Grammar.Sum.TCB        Σ public
    using (inj₁ ; inj₂)
