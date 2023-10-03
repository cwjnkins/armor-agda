{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.Extension.KU.TCB
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Properties
open import Aeres.Data.X690-DER.BitString
open import Aeres.Data.X690-DER.SequenceOf

open import Aeres.Prelude

module Aeres.Data.X509.Extension.KU.Properties where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Properties  UInt8

@0 unambiguousKUFields : Unambiguous KUFields
unambiguousKUFields = TLV.unambiguous (TLV.unambiguous BitString.unambiguous)

@0 nonmalleableKUFields : NonMalleable RawKUFields
nonmalleableKUFields = TLV.nonmalleable BitString.nonmalleable
