import      Aeres.Grammar.Seq.MaximalParser
import      Aeres.Grammar.Seq.Parser
import      Aeres.Grammar.Seq.Properties
import      Aeres.Grammar.Seq.TCB
open import Aeres.Prelude

module Aeres.Grammar.Seq (Σ : Set) where

open Aeres.Grammar.Seq.Parser Σ public
open Aeres.Grammar.Seq.TCB    Σ public

module Seq where
  open import Aeres.Grammar.Seq.Properties Σ public

  module MaximalParser where
    open Aeres.Grammar.Seq.MaximalParser Σ public
