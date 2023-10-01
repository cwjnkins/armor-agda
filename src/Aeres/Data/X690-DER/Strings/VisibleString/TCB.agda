{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions.NonMalleable
import      Aeres.Grammar.IList
open import Aeres.Prelude

module Aeres.Data.X690-DER.Strings.VisibleString.TCB where

open Aeres.Grammar.IList UInt8
open Aeres.Grammar.Definitions.NonMalleable UInt8

record VisibleStringValue (@0 bs : List UInt8) : Set where
  constructor mkVisibleStringValue
  field
    chars : List UInt8
    @0 range : All (InRange 32 127) chars
    @0 bs≡ : bs ≡ chars

  size : ℕ
  size = length chars

VisibleString = TLV Tag.VisibleString VisibleStringValue

RawVisibleStringValue : Raw VisibleStringValue
Raw.D RawVisibleStringValue = List UInt8
Raw.to RawVisibleStringValue = VisibleStringValue.chars

RawVisibleString : Raw VisibleString 
RawVisibleString = RawTLV _ RawVisibleStringValue
