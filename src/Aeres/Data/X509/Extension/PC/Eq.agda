{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.Extension.PC.Properties
open import Aeres.Data.X509.Extension.PC.TCB
open import Aeres.Data.X690-DER.Int
import      Aeres.Data.X690-DER.OctetString.Properties
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
open import Aeres.Prelude

module Aeres.Data.X509.Extension.PC.Eq where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8

instance
  eq≋ : Eq≋ PCFieldsSeqFields
  eq≋ = isoEq≋ iso (eq≋&ₚ it it)
