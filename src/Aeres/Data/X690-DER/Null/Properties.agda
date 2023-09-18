{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.Null.TCB
import      Aeres.Data.X690-DER.TLV.Properties as TLV
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Definitions.NonMalleable
open import Aeres.Prelude
import      Data.Nat.Properties     as Nat

module Aeres.Data.X690-DER.Null.Properties where

open Aeres.Grammar.Definitions              UInt8
open Aeres.Grammar.Definitions.NonMalleable UInt8

@0 unambiguous : Unambiguous Null
unambiguous = TLV.unambiguous λ where refl refl → refl

@0 nonmalleableValue : NonMalleable (_≡ []) RawNull
NonMalleable.unambiguous nonmalleableValue = λ where refl refl → refl
NonMalleable.injective nonmalleableValue (─ .[] , refl) (─ .[] , refl) _ = refl

@0 nonmalleable : NonMalleable Null _
nonmalleable = TLV.nonmalleable nonmalleableValue

instance
  eq≋ : Eq≋ (_≡ [])
  Eq≋._≋?_ eq≋ refl refl = yes ≋-refl
