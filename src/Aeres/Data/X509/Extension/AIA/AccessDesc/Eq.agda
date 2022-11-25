{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.Extension.AIA.AccessDesc.AccessMethod
open import Aeres.Data.X509.Extension.AIA.AccessDesc.Properties
open import Aeres.Data.X509.Extension.AIA.AccessDesc.TCB
open import Aeres.Data.X509.GeneralName
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
open import Aeres.Prelude

module Aeres.Data.X509.Extension.AIA.AccessDesc.Eq where

open Aeres.Grammar.Definitions UInt8

instance
  eq≋ : Eq≋ AccessDescFields
  eq≋ = isoEq≋ iso (eq≋&ₚ it it)
