{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.Strings.BMPString.TCB
open import Aeres.Data.X690-DER.TLV.TCB
open import Aeres.Data.X690-DER.TLV as TLV
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Data.Unicode.UTF16.Properties as UTF16
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Definitions.NonMalleable
import      Aeres.Grammar.IList
open import Aeres.Prelude

module Aeres.Data.X690-DER.Strings.BMPString.Properties where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Definitions.NonMalleable UInt8
open Aeres.Grammar.IList       UInt8

@0 nonmalleableBMPString : NonMalleable BMPString RawBMPString
nonmalleableBMPString = TLV.nonmalleable UTF16.nonmalleable
