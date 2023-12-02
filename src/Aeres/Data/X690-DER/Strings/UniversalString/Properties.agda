open import Aeres.Binary
open import Aeres.Data.X690-DER.Strings.UniversalString.TCB
import      Aeres.Data.X690-DER.TLV.Properties as TLV
import      Aeres.Data.Unicode.UTF32.Properties as UTF32
import      Aeres.Grammar.Definitions.NonMalleable.Base
open import Aeres.Prelude

module Aeres.Data.X690-DER.Strings.UniversalString.Properties where

open Aeres.Grammar.Definitions.NonMalleable.Base UInt8

@0 nonmalleable : NonMalleable RawUniversalString
nonmalleable = TLV.nonmalleable UTF32.nonmalleable
