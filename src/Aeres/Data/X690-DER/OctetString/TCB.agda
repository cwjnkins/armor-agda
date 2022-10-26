{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Prelude

module Aeres.Data.X690-DER.OctetString.TCB where

OctetStringValue : @0 List UInt8 → Set
OctetStringValue = Singleton

OctetString = TLV Tag.OctetString OctetStringValue
