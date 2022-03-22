{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509
import      Aeres.Data.X509.Properties.GeneralName as GeneralNameProps
import      Aeres.Data.X509.Properties.OctetstringValue as OSProps
import      Aeres.Data.X509.Properties.Primitives as PrimProps
import      Aeres.Data.X509.Properties.TLV as TLVProps
open import Aeres.Prelude

module Aeres.Data.X509.Properties.NCFieldsSeqFields where

open Base256
open import Aeres.Grammar.Definitions Dig
open import Aeres.Grammar.Properties  Dig

postulate
  @0 unambiguous : Unambiguous X509.NCFieldsSeqFields
