open import Aeres.Binary
open import Aeres.Data.X509.Extension.INAP.TCB
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Properties
open import Aeres.Data.X690-DER.Int

open import Aeres.Prelude

module Aeres.Data.X509.Extension.INAP.Properties where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Properties  UInt8

@0 unambiguous : Unambiguous INAPFields
unambiguous = TLV.unambiguous Int.unambiguous

@0 nonmalleable : NonMalleable RawINAPFields
nonmalleable = TLV.nonmalleable Int.nonmalleable
