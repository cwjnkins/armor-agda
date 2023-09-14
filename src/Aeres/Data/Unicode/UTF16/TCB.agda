{-# OPTIONS --subtyping #-}

open import Aeres.Binary
import      Aeres.Grammar.IList.TCB
open import Aeres.Prelude

module Aeres.Data.Unicode.UTF16.TCB where

-- We only support the BMP restriction of UTF16

open Aeres.Grammar.IList.TCB UInt8

record BMPChar (@0 bs : List UInt8) : Set where
  constructor mkBMPChar
  field
    c₁ c₂ : UInt8
    @0 range : InRange 0 215 c₁ ⊎ InRange 224 255 c₁
    @0 bs≡ : bs ≡ c₁ ∷ [ c₂ ]

BMP : @0 List UInt8 → Set
BMP = IList BMPChar

size : ∀ {@0 bs} → BMP bs → ℕ
size bmp = lengthIList bmp
