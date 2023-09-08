{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.Strings.PrintableString.Char
open import Aeres.Data.X690-DER.Strings.PrintableString.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.IList
open import Aeres.Prelude

module Aeres.Data.X690-DER.Strings.PrintableString.Properties where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.IList       UInt8

instance
  PrintableStringEq≋ : Eq≋ (IList PrintableStringChar)
  PrintableStringEq≋ = IList.IListEq≋
