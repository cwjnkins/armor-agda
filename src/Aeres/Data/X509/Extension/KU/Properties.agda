open import Aeres.Binary
open import Aeres.Data.X509.Extension.KU.TCB
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Properties
open import Aeres.Data.X690-DER.BitString
open import Aeres.Data.X690-DER.SequenceOf

open import Aeres.Prelude

module Aeres.Data.X509.Extension.KU.Properties where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Properties  UInt8

@0 unambiguous : Unambiguous KUFields
unambiguous = TLV.unambiguous BitString.unambiguous

@0 nonmalleable : NonMalleable RawKUFields
nonmalleable = TLV.nonmalleable BitString.nonmalleable
