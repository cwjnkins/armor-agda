open import Aeres.Binary
open import Aeres.Data.X509.Extension.SKI.TCB
open import Aeres.Data.X690-DER.OctetString
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Properties

open import Aeres.Prelude

module Aeres.Data.X509.Extension.SKI.Properties where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Properties  UInt8

@0 unambiguous : Unambiguous SKIFields
unambiguous = TLV.unambiguous OctetString.unambiguous

@0 nonmalleable : NonMalleable RawSKIFields
nonmalleable = TLV.nonmalleable OctetString.nonmalleable
