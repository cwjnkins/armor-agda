{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.Unicode.UTF8.TCB
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions.NonMalleable
open import Aeres.Data.X690-DER.TLV.TCB
open import Aeres.Prelude

module Aeres.Data.X690-DER.Strings.UTF8String.TCB where

open Aeres.Grammar.Definitions.NonMalleable UInt8

UTF8String : @0 List UInt8 → Set
UTF8String = TLV Tag.UTF8String UTF8

RawUTF8String : Raw UTF8String 
RawUTF8String = RawTLV RawUTF8
