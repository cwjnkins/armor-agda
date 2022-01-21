{-# OPTIONS --subtyping #-}

import      Aeres.Binary
open import Aeres.Data.X509
import      Aeres.Grammar.Definitions
open import Aeres.Prelude

module Aeres.Data.X509.Semantic.Cert where

open Aeres.Binary
open Base256
open Aeres.Grammar.Definitions Dig

SCP2 : ∀ {@0 bs} → X509.Cert bs → Set
SCP2 c = T (isSome (proj₂ (X509.Cert.getExtensions c))) → X509.Cert.getVersion c ≡ ℤ.+ 2

scp2 : ∀ {@0 bs} (c : X509.Cert bs) → Dec (SCP2 c)
scp2 c
  with isSome (proj₂ (X509.Cert.getExtensions c))
... | false = yes (λ ())
... | true
  with X509.Cert.getVersion c
... | v
  with v ≟ ℤ.+ 2
... | yes v≡ = yes (λ _ → v≡)
... | no ¬v≡ = no (λ abs → contradiction (abs tt) ¬v≡)
