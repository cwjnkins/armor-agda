{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.Tag
open import Aeres.Data.X690-DER.TLV
open import Aeres.Prelude

module Aeres.Data.X690-DER.Boool.TCB where

data BoolRep : Bool → UInt8 → Set where
  falseᵣ : BoolRep false (# 0)
  trueᵣ  : BoolRep true (# 255)

record BoolValue (@0 bs : List UInt8) : Set where
  constructor mkBoolValue
  field
    v     : Bool
    @0 b  : UInt8
    @0 vᵣ : BoolRep v b
    @0 bs≡ : bs ≡ [ b ]

Boool = TLV Tag.Boolean BoolValue
