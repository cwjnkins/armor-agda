{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.Extension.PM.Properties
open import Aeres.Data.X509.Extension.PM.TCB
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Data.X690-DER.SequenceOf.TCB
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Seq
open import Aeres.Prelude

module Aeres.Data.X509.Extension.PM.Eq where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Seq         UInt8

instance
  eq≋ : Eq≋ PolicyMapFields
  eq≋ = Iso.isoEq≋ iso (Seq.eq≋&ₚ it it)
