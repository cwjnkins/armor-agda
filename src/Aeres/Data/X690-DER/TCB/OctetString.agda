{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.TLV
open import Aeres.Data.X690-DER.Tag
open import Aeres.Prelude

module Aeres.Data.X690-DER.TCB.OctetString where

open Base256

OctetStringValue : @0 List UInt8 → Set
OctetStringValue = Singleton

OctetString = TLV Tag.OctetString OctetStringValue
