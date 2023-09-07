{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.Length.TCB
open import Aeres.Data.X690-DER.Null.TCB
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
open import Aeres.Prelude
import      Data.Nat.Properties     as Nat

module Aeres.Data.X690-DER.Null.Properties where

open Aeres.Grammar.Definitions UInt8

@0 unambiguous : Unambiguous Null
unambiguous = TLV.unambiguous λ where refl refl → refl

instance
  eq≋ : Eq≋ (_≡ [])
  Eq≋._≋?_ eq≋ refl refl = yes ≋-refl
