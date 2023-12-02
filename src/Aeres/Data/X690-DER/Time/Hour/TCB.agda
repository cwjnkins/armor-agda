open import Aeres.Binary
open import Aeres.Data.X690-DER.Time.TimeType.TCB
import      Aeres.Grammar.Definitions.NonMalleable
open import Aeres.Prelude

module Aeres.Data.X690-DER.Time.Hour.TCB where

open Aeres.Grammar.Definitions.NonMalleable UInt8

Hour : @0 List UInt8 → Set
Hour = TimeType 2 0 23

RawHour : Raw Hour
RawHour = RawTimeType _ _ _
