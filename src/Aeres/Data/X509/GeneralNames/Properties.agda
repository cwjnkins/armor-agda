open import Aeres.Binary
open import Aeres.Data.X509.GeneralNames.TCB
open import Aeres.Data.X509.GeneralNames.GeneralName
open import Aeres.Data.X509.Name
open import Aeres.Data.X690-DER
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Sum
open import Aeres.Prelude
open import Data.Nat.Properties
  hiding (_≟_)

module Aeres.Data.X509.GeneralNames.Properties where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Properties  UInt8
open Aeres.Grammar.Sum         UInt8

module GeneralNamesElems where
  @0 unambiguous : Unambiguous GeneralNamesElems
  unambiguous =
    SequenceOf.Bounded.unambiguous
      GeneralName.unambiguous GeneralName.nonempty GeneralName.nosubstrings

  @0 nonmalleable : NonMalleable RawGeneralNamesElems
  nonmalleable = SequenceOf.Bounded.nonmalleable{R = RawGeneralName} GeneralName.nonempty GeneralName.nosubstrings GeneralName.nonmalleable

@0 unambiguous : Unambiguous GeneralNames
unambiguous = TLV.unambiguous GeneralNamesElems.unambiguous

@0 nonmalleable : NonMalleable RawGeneralNames
nonmalleable = TLV.nonmalleable{R = RawGeneralNamesElems} GeneralNamesElems.nonmalleable
