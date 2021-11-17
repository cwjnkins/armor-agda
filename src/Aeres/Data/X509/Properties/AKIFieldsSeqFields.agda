{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Prelude

module Aeres.Data.X509.Properties.AKIFieldsSeqFields where

open Base256
open import Aeres.Grammar.Definitions Dig

equivalent : Equivalent (&ₚ (Option X509.AKIKeyId) (&ₚ (Option X509.AKIAuthCertIssuer) (Option X509.AKIAuthCertSN))) X509.AKIFieldsSeqFields
proj₁ equivalent (mk&ₚ v₁ (mk&ₚ v₂ v₃ refl) refl) = X509.mkAKIFieldsSeqFields v₁ v₂ v₃ refl
proj₂ equivalent (X509.mkAKIFieldsSeqFields v₁ v₂ v₃ refl) = mk&ₚ v₁ (mk&ₚ v₂ v₃ refl) refl

postulate
  @0 unambiguous : Unambiguous X509.AKIFieldsSeqFields
