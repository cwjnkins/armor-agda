{-# OPTIONS --subtyping #-}

import      Aeres.Grammar.Definitions.Eq
import      Aeres.Grammar.Definitions.Iso
import      Aeres.Grammar.Definitions.NoConfusion
import      Aeres.Grammar.Definitions.NoOverlap
import      Aeres.Grammar.Definitions.NoSubstrings
import      Aeres.Grammar.Definitions.NonMalleable
import      Aeres.Grammar.Definitions.NonEmpty
import      Aeres.Grammar.Definitions.Unambiguous
open import Aeres.Prelude

module Aeres.Grammar.Definitions (Σ : Set) where

open Aeres.Grammar.Definitions.Eq           Σ public
open Aeres.Grammar.Definitions.Iso          Σ public
open Aeres.Grammar.Definitions.NoOverlap    Σ public
open Aeres.Grammar.Definitions.NoConfusion  Σ public
open Aeres.Grammar.Definitions.NoSubstrings Σ public
open Aeres.Grammar.Definitions.NonEmpty     Σ public
open Aeres.Grammar.Definitions.NonMalleable Σ public
open Aeres.Grammar.Definitions.Unambiguous  Σ public
