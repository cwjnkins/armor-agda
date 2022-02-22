{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.TCB.TLV
import      Aeres.Data.X690-DER.TCB.Tag as Tag
open import Aeres.Prelude

module Aeres.Data.X690-DER.TCB.OctetString where

open Base256

OctetStringValue : @0 List UInt8 → Set
OctetStringValue = Singleton

OctetString = TLV Tag.OctetString OctetStringValue
