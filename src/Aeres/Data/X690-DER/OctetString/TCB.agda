{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions.NonMalleable
open import Aeres.Prelude

module Aeres.Data.X690-DER.OctetString.TCB where

open Aeres.Grammar.Definitions.NonMalleable UInt8

OctetStringValue : @0 List UInt8 → Set
OctetStringValue = Singleton

OctetString = TLV Tag.OctetString OctetStringValue

RawOctetStringValue : Raw OctetStringValue
Raw.D RawOctetStringValue = List UInt8
Raw.to RawOctetStringValue = ↑_

RawOctetString : Raw OctetString
RawOctetString = RawTLV _ RawOctetStringValue
