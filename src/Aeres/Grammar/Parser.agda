{-# OPTIONS --subtyping #-}

open import Aeres.Prelude
import Aeres.Grammar.Parser.Bounded
import Aeres.Grammar.Parser.IList
import Aeres.Grammar.Parser.Maximal
import Aeres.Grammar.Parser.Option
import Aeres.Grammar.Parser.Pair
import Aeres.Grammar.Parser.Sigma
import Aeres.Grammar.Parser.Sum
import Aeres.Grammar.Parser.WellFounded
import Aeres.Grammar.Parser.While

module Aeres.Grammar.Parser (Σ : Set) where

open import Aeres.Grammar.Parser.Core Σ public

open Aeres.Grammar.Parser.Bounded     Σ public
open Aeres.Grammar.Parser.IList       Σ public
open Aeres.Grammar.Parser.Maximal     Σ public
open Aeres.Grammar.Parser.Option      Σ public
open Aeres.Grammar.Parser.Pair        Σ public
open Aeres.Grammar.Parser.Sigma       Σ public
open Aeres.Grammar.Parser.Sum         Σ public
open Aeres.Grammar.Parser.WellFounded Σ public
open Aeres.Grammar.Parser.While       Σ public

