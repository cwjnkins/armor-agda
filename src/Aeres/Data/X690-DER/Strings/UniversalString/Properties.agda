{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.Strings.UniversalString.TCB
open import Aeres.Data.X690-DER.TLV.TCB
open import Aeres.Data.X690-DER.TLV as TLV
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Data.Unicode.UTF32.Properties as UTF32
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Definitions.NonMalleable
import      Aeres.Grammar.IList
open import Aeres.Prelude

module Aeres.Data.X690-DER.Strings.UniversalString.Properties where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Definitions.NonMalleable UInt8
open Aeres.Grammar.IList       UInt8

@0 nonmalleableUniversalString : NonMalleable UniversalString RawUniversalString
nonmalleableUniversalString = TLV.nonmalleable UTF32.nonmalleable
