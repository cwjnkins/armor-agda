{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Prelude

module Aeres.Data.X690-DER.Int where

open Base256

module Int where
  open import Aeres.Data.X690-DER.TCB.Int public
open Int public
  hiding (getVal)
