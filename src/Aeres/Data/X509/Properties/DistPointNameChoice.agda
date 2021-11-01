{-# OPTIONS --subtyping #-}

import Aeres.Data.X509.Properties.TLV as TLVprops
open import Aeres.Prelude
open import Aeres.Binary
open import Aeres.Data.X509
open import Data.Nat.Properties
  hiding (_≟_)

module Aeres.Data.X509.Properties.DistPointNameChoice where

open Base256
open import Aeres.Grammar.Definitions Dig
open import Aeres.Grammar.Sum         Dig

nonnesting : NonNesting X509.DistPointNameChoice
nonnesting x (X509.fullname x₁) (X509.fullname x₂) = ‼ TLVprops.nonnesting x x₁ x₂
nonnesting x (X509.fullname x₁) (X509.nameRTCrlissr x₂) = ⊥-elim (TLVprops.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.nameRTCrlissr x₁) (X509.fullname x₂) = ⊥-elim (TLVprops.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (X509.nameRTCrlissr x₁) (X509.nameRTCrlissr x₂) = ‼ TLVprops.nonnesting x x₁ x₂

postulate
  equivalent : Equivalent (Sum X509.FullName X509.NameRTCrlIssuer) X509.DistPointNameChoice
