open import Aeres.Binary
open import Aeres.Data.X690-DER.Time.TimeType.TCB
import      Aeres.Grammar.Definitions.NonMalleable
open import Aeres.Prelude

module Aeres.Data.X690-DER.Time.Day.TCB where

open Aeres.Grammar.Definitions.NonMalleable UInt8

Day : @0 List UInt8 → Set
Day = TimeType 2 1 31

RawDay : Raw Day
RawDay = RawTimeType _ _ _
