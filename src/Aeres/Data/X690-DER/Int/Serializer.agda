{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.Int.TCB
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Serializer
open import Aeres.Prelude

module Aeres.Data.X690-DER.Int.Serializer where

open Aeres.Grammar.Serializer UInt8

serializeVal : Serializer IntegerValue
serializeVal = id

serialize : Serializer Int
serialize = TLV.serialize serializeVal
