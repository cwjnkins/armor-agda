{-# OPTIONS --subtyping #-}

open import Aeres.Prelude
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Grammar.Parser (Σ : Set) where

open import Aeres.Grammar.Parser.Core Σ public

open import Aeres.Grammar.Parser.Bounded Σ public
open import Aeres.Grammar.Parser.Option Σ public
open import Aeres.Grammar.Parser.Pair Σ public
open import Aeres.Grammar.Parser.WellFounded Σ public
open import Aeres.Grammar.Parser.While Σ public

