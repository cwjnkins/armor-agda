{-# OPTIONS --subtyping #-}

import Aeres.Grammar.IList.All
import Aeres.Grammar.IList.Parser
import Aeres.Grammar.IList.Properties
import Aeres.Grammar.IList.Serializer
import Aeres.Grammar.IList.TCB

module Aeres.Grammar.IList (Σ : Set) where

module IList where
  open Aeres.Grammar.IList.All        Σ public
  open Aeres.Grammar.IList.Properties Σ public
  open Aeres.Grammar.IList.TCB.IList  Σ public

open Aeres.Grammar.IList.Parser       Σ public
open Aeres.Grammar.IList.Serializer   Σ public
open Aeres.Grammar.IList.TCB          Σ public
  hiding (module IList)
