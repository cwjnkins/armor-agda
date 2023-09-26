{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.Strings.UTF8String.TCB
open import Aeres.Data.X690-DER.TLV.TCB
open import Aeres.Data.X690-DER.TLV as TLV
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Data.Unicode.UTF8.Properties as UTF8
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Definitions.NonMalleable
import      Aeres.Grammar.IList
open import Aeres.Prelude

module Aeres.Data.X690-DER.Strings.UTF8String.Properties where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Definitions.NonMalleable UInt8
open Aeres.Grammar.IList       UInt8

@0 nonmalleableUTF8String : NonMalleable UTF8String RawUTF8String
nonmalleableUTF8String = TLV.nonmalleable UTF8.nonmalleable
