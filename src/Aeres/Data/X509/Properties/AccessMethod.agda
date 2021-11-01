{-# OPTIONS --subtyping #-}


open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Prelude

module Aeres.Data.X509.Properties.AccessMethod where

open Base256
open import Aeres.Grammar.Definitions Dig


@0 nonnesting : NonNesting X509.AccessMethod
nonnesting x (X509.caissid x₁) (X509.caissid x₂) = trans x₁ (sym x₂)
nonnesting () (X509.caissid refl) (X509.ocspid refl)
nonnesting () (X509.ocspid refl) (X509.caissid refl)
nonnesting x (X509.ocspid x₁) (X509.ocspid x₂) = trans x₁ (sym x₂)
