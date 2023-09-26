{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.Unicode.UTF16
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions.NonMalleable
import      Aeres.Grammar.IList.TCB
import      Aeres.Grammar.Sum.TCB
open import Aeres.Prelude

module Aeres.Data.X690-DER.Strings.BMPString.TCB where

open Aeres.Grammar.IList.TCB UInt8
open Aeres.Grammar.Definitions.NonMalleable UInt8

BMPString : @0 List UInt8 → Set
BMPString xs = TLV Tag.BMPString BMP xs

RawBMPString : Raw BMPString 
RawBMPString = RawTLV RawBMP
