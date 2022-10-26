{-# OPTIONS --subtyping #-}

open import Aeres.Binary
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Data.X690-DER.TLV
open import Aeres.Prelude

module Aeres.Data.X690-DER.Int.TCB where

open Base256

-- TODO: IntegerValue = Singleton ∘ twosComplement
--
-- To be part of a full TLS/SSL stack the parser should convert the
-- serialization to a convenient data structure. Instead, we do it with `getVal`
-- below (so every access potentially triggers the decoding)
IntegerValue : @0 List UInt8 → Set
IntegerValue = Singleton

pattern mkIntegerValue x y = singleton x y

Int : @0 List UInt8 → Set
Int = TLV Tag.Integer IntegerValue

getVal : ∀ {@0 bs} → Int bs → ℤ
getVal = twosComplement ∘ Singleton.x ∘ TLV.val
