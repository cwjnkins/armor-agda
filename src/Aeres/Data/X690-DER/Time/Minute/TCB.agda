{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.Time.TimeType.TCB
import      Aeres.Grammar.Definitions.NonMalleable
open import Aeres.Prelude

module Aeres.Data.X690-DER.Time.Minute.TCB where

open Aeres.Grammar.Definitions.NonMalleable UInt8

Minute : @0 List UInt8 → Set
Minute = TimeType 2 0 59

RawMinute : Raw Minute
RawMinute = RawTimeType _ _ _
