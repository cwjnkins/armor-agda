{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Prelude
open import Aeres.Data.UTF8
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Data.X690-DER.OctetString

module Aeres.Data.X509.Strings.TCB where

TeletexString : @0 List UInt8 → Set
TeletexString xs = TLV Tag.TeletexString  OctetStringValue xs

UniversalString : @0 List UInt8 → Set
UniversalString xs = TLV Tag.UniversalString  UTF8 xs

UTF8String : @0 List UInt8 → Set
UTF8String xs = TLV Tag.UTF8String  UTF8 xs

BMPString : @0 List UInt8 → Set
BMPString xs = TLV Tag.BMPString  UTF8 xs

-- TODO: check this (is it UTF8?)
VisibleString : @0 List UInt8 → Set
VisibleString xs = TLV Tag.VisibleString  UTF8 xs
