open import Aeres.Binary
open import Aeres.Data.X509.Extension.NC.GeneralSubtree
open import Aeres.Data.X509.Extension.NC.Properties
open import Aeres.Data.X509.Extension.NC.TCB
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Data.X690-DER.SequenceOf
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
import      Aeres.Grammar.Seq
open import Aeres.Prelude

module Aeres.Data.X509.Extension.NC.Eq where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8
open Aeres.Grammar.Seq         UInt8

instance
  eq≋ : Eq≋ NCFieldsSeqFields
  eq≋ = Iso.isoEq≋ iso (Seq.eq≋&ₚ it it)
    where
    instance
      e : Eq≋ (NonEmptySequenceOf GeneralSubtree)
      e = SequenceOf.BoundedSequenceOfEq≋ ⦃ it ⦄
