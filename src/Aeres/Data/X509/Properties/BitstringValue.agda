{-# OPTIONS --subtyping #-}

open import Aeres.Prelude
open import Aeres.Binary
open import Aeres.Data.X509
import      Aeres.Grammar.Definitions
open import Data.Nat.Properties
  hiding (_≟_)

module Aeres.Data.X509.Properties.BitstringValue where

open Base256
open Aeres.Grammar.Definitions Dig

postulate
  @0 unambiguous : Unambiguous Generic.BitstringValue

