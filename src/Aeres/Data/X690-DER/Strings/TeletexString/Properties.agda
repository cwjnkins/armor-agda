open import Aeres.Binary
open import Aeres.Data.X690-DER.Strings.TeletexString.TCB
import      Aeres.Data.X690-DER.TLV.Properties as TLV
import      Aeres.Grammar.Definitions.NonMalleable.Base
import      Aeres.Data.X690-DER.OctetString.Properties as OctetString
open import Aeres.Prelude

module Aeres.Data.X690-DER.Strings.TeletexString.Properties where

open Aeres.Grammar.Definitions.NonMalleable.Base UInt8

@0 nonmalleable : NonMalleable RawTeletexString
nonmalleable = TLV.nonmalleable OctetString.nonmalleableValue
