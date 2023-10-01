{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.GeneralName.Properties
open import Aeres.Data.X509.GeneralName.TCB
  hiding (module GeneralName)
open import Aeres.Data.X509.RDN
open import Aeres.Data.X690-DER
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Sum
open import Aeres.Prelude
open import Data.Nat.Properties
  hiding (_≟_)

module Aeres.Data.X509.GeneralName.Eq where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Sum         UInt8

instance
  eq≋ : Eq≋ GeneralName
  eq≋ =
    Iso.isoEq≋ iso
      (Sum.sumEq≋ ⦃ eq₂ =
       Sum.sumEq≋ ⦃ eq₂ =
       Sum.sumEq≋ ⦃ eq₂ =
       Sum.sumEq≋ ⦃ eq₂ =
       Sum.sumEq≋ ⦃ eq₂ =
       Sum.sumEq≋ ⦃ eq₂ =
       Sum.sumEq≋ ⦃ eq₂ = Sum.sumEq≋ ⦄ ⦄ ⦄ ⦄ ⦄ ⦄ ⦄)

  eq≋Elems : Eq≋ GeneralNamesElems
  eq≋Elems = SequenceOf.BoundedSequenceOfEq≋
