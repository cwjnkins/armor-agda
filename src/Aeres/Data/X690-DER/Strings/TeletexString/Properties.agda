{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.Strings.TeletexString.TCB
open import Aeres.Data.X690-DER.TLV.TCB
open import Aeres.Data.X690-DER.TLV as TLV
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Definitions.NonMalleable
open import Aeres.Data.X690-DER.OctetString.Properties as OS
import      Aeres.Grammar.IList
open import Aeres.Prelude

module Aeres.Data.X690-DER.Strings.TeletexString.Properties where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Definitions.NonMalleable UInt8
open Aeres.Grammar.IList       UInt8

@0 nonmalleableTeletexString : NonMalleable TeletexString RawTeletexString
nonmalleableTeletexString = TLV.nonmalleable OS.nonmalleableValue
