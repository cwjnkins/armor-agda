{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Prelude

module Aeres.Data.X509.Properties.BCFieldsSeqFields where

open Base256
open import Aeres.Grammar.Definitions Dig


equivalent : Equivalent (&ₚ (Option Generic.Boool) (Option Generic.Int)) X509.BCFieldsSeqFields
proj₁ equivalent (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = X509.mkBCFieldsSeqFields fstₚ₁ sndₚ₁ bs≡
proj₂ equivalent (X509.mkBCFieldsSeqFields bcca bcpathlen bs≡) = mk&ₚ bcca bcpathlen bs≡
