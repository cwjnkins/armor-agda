{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.OctetString.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions.NonMalleable
open import Aeres.Prelude

module Aeres.Data.X509.Extension.SKI.TCB where

open Aeres.Grammar.Definitions.NonMalleable UInt8

SKIFields : @0 List UInt8 → Set
SKIFields = TLV Tag.OctetString OctetString

RawSKIFields : Raw SKIFields
RawSKIFields = RawTLV _ RawOctetString
