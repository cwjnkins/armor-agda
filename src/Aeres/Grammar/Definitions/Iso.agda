{-# OPTIONS --subtyping #-}

import Aeres.Grammar.Definitions.Iso.Base
import Aeres.Grammar.Definitions.Iso.Properties

module Aeres.Grammar.Definitions.Iso (Σ : Set) where

open Aeres.Grammar.Definitions.Iso.Base Σ public

module Iso where
  open Aeres.Grammar.Definitions.Iso.Properties Σ public
