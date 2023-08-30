{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Prelude
open import Aeres.Data.UTF8
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Data.X690-DER.OctetString
import Aeres.Grammar.Definitions
import Aeres.Grammar.IList.TCB
import Aeres.Grammar.Sum.TCB

module Aeres.Data.X509.Strings.TCB where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.IList.TCB   UInt8
open Aeres.Grammar.Sum.TCB     UInt8

TeletexString : @0 List UInt8 → Set
TeletexString xs = TLV Tag.TeletexString  OctetStringValue xs

UniversalString : @0 List UInt8 → Set
UniversalString xs = TLV Tag.UniversalString  UTF8 xs

UTF8String : @0 List UInt8 → Set
UTF8String xs = TLV Tag.UTF8String  UTF8 xs

record BMPChar (@0 bs : List UInt8) : Set where
  constructor mkBMPChar
  field
    c₁ c₂ : UInt8
    @0 range : InRange 0 215 c₁ ⊎ InRange 224 255 c₁
    @0 bs≡ : bs ≡ c₁ ∷ [ c₂ ]

BMP : @0 List UInt8 → Set
BMP = IList BMPChar

BMPString : @0 List UInt8 → Set
BMPString xs = TLV Tag.BMPString BMP xs

-- TODO: check this (is it UTF8?)
VisibleString : @0 List UInt8 → Set
VisibleString xs = TLV Tag.VisibleString  UTF8 xs
