{-# OPTIONS --subtyping #-}

open import Aeres.Binary
import      Aeres.Data.X690-DER.TCB.Tag as Tag
open import Aeres.Data.X690-DER.TCB.TLV
open import Aeres.Prelude

module Aeres.Data.X690-DER.TCB.Int where

open Base256

IntegerValue : @0 List UInt8 → Set
IntegerValue bs = Singleton (twosComplement bs)

pattern mkIntegerValue x y = singleton x y

Int : @0 List UInt8 → Set
Int = TLV Tag.Integer IntegerValue

getVal : ∀ {@0 bs} → Int bs → ℤ
getVal i = Singleton.x (TLV.val i)
