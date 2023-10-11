{-# OPTIONS --subtyping #-}

open import Aeres.Binary
import      Aeres.Data.X690-DER.Length.Properties as Length
open import Aeres.Data.X690-DER.Length.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions.NonMalleable
open import Aeres.Prelude

module Aeres.Data.X690-DER.Null.TCB where

open Aeres.Grammar.Definitions.NonMalleable UInt8

Null = TLV Tag.Null (_≡ [])

nullTLV : Null (Tag.Null ∷ [ # 0 ])
nullTLV = mkTLV (Length.shortₛ (# 0)) refl refl refl

RawNull : Raw Null
RawNull = RawTLV _ RawSubSingleton
