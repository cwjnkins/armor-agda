{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.Strings.PrintableString.Char.TCB
import      Aeres.Grammar.Definitions.NonMalleable
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.IList
open import Aeres.Prelude

module Aeres.Data.X690-DER.Strings.PrintableString.TCB where

open Aeres.Grammar.IList UInt8
open Aeres.Grammar.Definitions.NonMalleable UInt8

PrintableString : @0 List UInt8 → Set
PrintableString = TLV Tag.PrintableString (IList PrintableStringChar)

size : ∀ {@0 bs} → IList PrintableStringChar bs → ℕ
size = lengthIList

RawPrintableStringValue : Raw (IList PrintableStringChar)
Raw.D RawPrintableStringValue = List UInt8
Raw.to RawPrintableStringValue = Raw.to (RawIList RawPrintableStringChar)

RawPrintableString : Raw PrintableString 
RawPrintableString = RawTLV RawPrintableStringValue
