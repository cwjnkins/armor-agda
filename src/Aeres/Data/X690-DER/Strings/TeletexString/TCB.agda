{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.OctetString.TCB
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Data.X690-DER.TLV.TCB
open import Aeres.Prelude

module Aeres.Data.X690-DER.Strings.TeletexString.TCB where

TeletexString : @0 List UInt8 → Set
TeletexString = TLV Tag.TeletexString OctetStringValue
