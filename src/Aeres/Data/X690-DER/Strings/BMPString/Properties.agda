open import Aeres.Binary
open import Aeres.Data.X690-DER.Strings.BMPString.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.TLV.Properties as TLV
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Data.Unicode.UTF16.Properties as UTF16
import      Aeres.Grammar.Definitions.NonMalleable.Base
open import Aeres.Prelude

module Aeres.Data.X690-DER.Strings.BMPString.Properties where

open Aeres.Grammar.Definitions.NonMalleable.Base UInt8

@0 nonmalleable : NonMalleable RawBMPString
nonmalleable = TLV.nonmalleable UTF16.nonmalleable
