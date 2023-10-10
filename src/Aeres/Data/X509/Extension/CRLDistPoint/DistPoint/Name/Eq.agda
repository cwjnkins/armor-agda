{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.Extension.CRLDistPoint.DistPoint.Name.Properties
open import Aeres.Data.X509.Extension.CRLDistPoint.DistPoint.Name.TCB
open import Aeres.Data.X509.GeneralNames
open import Aeres.Data.X509.Name
open import Aeres.Data.X690-DER.SequenceOf
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Sum
open import Aeres.Prelude

module Aeres.Data.X509.Extension.CRLDistPoint.DistPoint.Name.Eq where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Sum         UInt8

instance
  eq≋ : Eq≋ DistPointNameChoice
  eq≋ = Iso.isoEq≋ iso Sum.sumEq≋
