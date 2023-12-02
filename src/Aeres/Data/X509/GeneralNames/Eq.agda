open import Aeres.Binary
open import Aeres.Data.X509.GeneralNames.TCB
open import Aeres.Data.X509.GeneralNames.GeneralName.Eq
open import Aeres.Data.X509.Name
open import Aeres.Data.X690-DER
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Sum
open import Aeres.Prelude
open import Data.Nat.Properties
  hiding (_≟_)

module Aeres.Data.X509.GeneralNames.Eq where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Sum         UInt8

instance
  eq≋Elems : Eq≋ GeneralNamesElems
  eq≋Elems = SequenceOf.BoundedSequenceOfEq≋
