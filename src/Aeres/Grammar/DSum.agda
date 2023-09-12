{-# OPTIONS --subtyping #-}

import      Aeres.Grammar.DSum.Parser
import      Aeres.Grammar.DSum.TCB

module Aeres.Grammar.DSum (Σ : Set) where

open Aeres.Grammar.DSum.TCB Σ    public
  hiding (module DSum)

module DSum where
  open Aeres.Grammar.DSum.Parser Σ public
