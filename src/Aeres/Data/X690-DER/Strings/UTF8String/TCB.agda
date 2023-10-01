{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.Unicode.UTF8.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions.NonMalleable.Base
open import Aeres.Prelude

module Aeres.Data.X690-DER.Strings.UTF8String.TCB where

open Aeres.Grammar.Definitions.NonMalleable.Base UInt8

UTF8String : @0 List UInt8 → Set
UTF8String = TLV Tag.UTF8String UTF8

RawUTF8String : Raw UTF8String 
RawUTF8String = RawTLV _ RawUTF8
