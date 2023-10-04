{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.Int.TCB
open import Aeres.Data.X690-DER.OctetString.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
open import Aeres.Prelude

module Aeres.Data.X509.Extension.INAP.TCB where

open      Aeres.Grammar.Definitions  UInt8

INAPFields : @0 List UInt8 → Set
INAPFields xs = TLV Tag.OctetString Int xs

RawINAPFields : Raw INAPFields
RawINAPFields = RawTLV _ RawInt
