{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.OctetString.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Grammar.Definitions.NonMalleable
open import Aeres.Data.X690-DER.Tag
open import Aeres.Prelude

module Aeres.Data.X690-DER.Strings.PrintableString.Char.TCB where

open Aeres.Grammar.Definitions.NonMalleable UInt8

data PrintableStringCharRange : @0 UInt8 → Set where
  space      : PrintableStringCharRange (# 32)
  apostrophe : PrintableStringCharRange (# 39)
  leftParen  : PrintableStringCharRange (# 40)
  rightParen : PrintableStringCharRange (# 41)
  plus       : PrintableStringCharRange (# 43)
  comma      : PrintableStringCharRange (# 44)
  hyphen     : PrintableStringCharRange (# 45)
  period     : PrintableStringCharRange (# 46)
  fslash     : PrintableStringCharRange (# 47)
  numbers    : ∀ {@0 c} → InRange 48 57 c → PrintableStringCharRange c
  colon      : PrintableStringCharRange (# 58)
  equals     : PrintableStringCharRange (# 61)
  question   : PrintableStringCharRange (# 63)
  uppers     : ∀ {@0 c} → InRange 65 90 c → PrintableStringCharRange c
  lowers     : ∀ {@0 c} → InRange 97 122 c → PrintableStringCharRange c

record PrintableStringChar (@0 bs : List UInt8) : Set where
  constructor mkPrintableStringChar
  field
    c : UInt8
    range : PrintableStringCharRange c
    @0 bs≡ : bs ≡ [ c ]

RawPrintableStringChar : Raw PrintableStringChar
Raw.D RawPrintableStringChar = UInt8
Raw.to RawPrintableStringChar = uncurry─ λ y → (PrintableStringChar.c y)
