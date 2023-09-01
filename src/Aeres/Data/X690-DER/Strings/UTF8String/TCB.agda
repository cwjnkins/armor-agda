{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.Unicode.UTF8.TCB
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Data.X690-DER.TLV.TCB
open import Aeres.Prelude

module Aeres.Data.X690-DER.Strings.UTF8String.TCB where

UTF8String : @0 List UInt8 → Set
UTF8String = TLV Tag.UTF8String UTF8
