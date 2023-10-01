{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.Strings.UTF8String.TCB
import      Aeres.Data.X690-DER.TLV.Properties as TLV
import      Aeres.Data.Unicode.UTF8.Properties as UTF8
import      Aeres.Grammar.Definitions.NonMalleable.Base
open import Aeres.Prelude

module Aeres.Data.X690-DER.Strings.UTF8String.Properties where

open Aeres.Grammar.Definitions.NonMalleable.Base UInt8

@0 nonmalleable : NonMalleable RawUTF8String
nonmalleable = TLV.nonmalleable UTF8.nonmalleable
