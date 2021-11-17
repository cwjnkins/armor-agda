{-# OPTIONS --subtyping #-}


open import Aeres.Binary
open import Aeres.Data.X509
import Aeres.Data.X509.Properties.TLV as TLVProps
import Aeres.Data.X509.Properties.PolicyQualifierInfoFields as PQIProps
open import Aeres.Prelude

module Aeres.Data.X509.Properties.PolicyInformationFields where
open ≡-Reasoning

open Base256
open import Aeres.Grammar.Definitions Dig
open import Aeres.Grammar.Sum         Dig

postulate
  @0 unambiguous : Unambiguous X509.PolicyInformationFields
