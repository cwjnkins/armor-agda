{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.BitString.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
import Aeres.Grammar.Definitions
open import Aeres.Prelude

module Aeres.Data.X509.Extension.KU.TCB where

open Aeres.Grammar.Definitions UInt8

KUFields : @0 List UInt8 → Set
KUFields xs = TLV Tag.OctetString BitString xs

RawKUFields : Raw KUFields
RawKUFields = RawTLV _ RawBitString
