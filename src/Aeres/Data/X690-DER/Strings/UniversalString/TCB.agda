{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Data.Unicode.UTF32.TCB
open import Aeres.Prelude

module Aeres.Data.X690-DER.Strings.UniversalString.TCB where

UniversalString : @0 List UInt8 → Set
UniversalString = TLV Tag.UniversalString UTF32
