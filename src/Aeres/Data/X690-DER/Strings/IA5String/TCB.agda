{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Data.X690-DER.OctetString.TCB
import      Aeres.Grammar.Definitions
open import Aeres.Prelude

module Aeres.Data.X690-DER.Strings.IA5String.TCB where

open Aeres.Grammar.Definitions UInt8

record IA5StringValue (@0 bs : List UInt8) : Set where
  constructor mkIA5StringValue
  field
    str : OctetStringValue bs
    @0 all<128 : True (All.all? (Fin._<? (# 128)) (↑ str))

  size : ℕ
  size = length (Singleton.x str)

IA5String : (@0 _ : List UInt8) → Set
IA5String xs = TLV Tag.IA5String IA5StringValue xs

RawIA5StringValue : Raw IA5StringValue
Raw.D RawIA5StringValue = List UInt8
Raw.to RawIA5StringValue = ↑_ ∘ IA5StringValue.str

RawIA5String : Raw IA5String 
RawIA5String = RawTLV _ RawIA5StringValue
