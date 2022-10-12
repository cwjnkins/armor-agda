{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.Int.TCB
open import Aeres.Grammar.Definitions UInt8
open import Aeres.Prelude

module Aeres.Data.X690-DER.Int.Properties where

unambiguous : Unambiguous IntegerValue
unambiguous self self = refl
