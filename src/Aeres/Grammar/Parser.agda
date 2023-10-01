{-# OPTIONS --subtyping #-}

open import Aeres.Prelude
import Aeres.Grammar.Parser.Lit
import Aeres.Grammar.Parser.Maximal
import Aeres.Grammar.Parser.WellFounded
import Aeres.Grammar.Parser.While

module Aeres.Grammar.Parser (Σ : Set) where

open import Aeres.Grammar.Parser.Core Σ public

open Aeres.Grammar.Parser.Lit         Σ public
open Aeres.Grammar.Parser.Maximal     Σ public
open Aeres.Grammar.Parser.WellFounded Σ public
open Aeres.Grammar.Parser.While       Σ public

