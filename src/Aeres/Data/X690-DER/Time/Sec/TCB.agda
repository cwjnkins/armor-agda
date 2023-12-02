open import Aeres.Binary
open import Aeres.Data.X690-DER.Time.TimeType.TCB
import      Aeres.Grammar.Definitions.NonMalleable
open import Aeres.Prelude

module Aeres.Data.X690-DER.Time.Sec.TCB where

open Aeres.Grammar.Definitions.NonMalleable UInt8

Sec : @0 List UInt8 → Set
Sec = TimeType 2 0 60

RawSec : Raw Sec
RawSec = RawTimeType _ _ _
