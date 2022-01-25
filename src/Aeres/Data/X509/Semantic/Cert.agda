{-# OPTIONS --subtyping #-}

import      Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Properties
import      Aeres.Grammar.Definitions
open import Aeres.Prelude

module Aeres.Data.X509.Semantic.Cert where

open Aeres.Binary
open Base256
open Aeres.Grammar.Definitions Dig

SCP1 : ∀ {@0 bs} → X509.Cert bs → Set
SCP1 c = X509.Cert.getTBSCertSignAlg c ≡ X509.Cert.getCertSignAlg c

scp1 :  ∀ {@0 bs} (c : X509.Cert bs) → Dec (SCP1 c)
scp1 c
  with proj₂ (X509.Cert.getTBSCertSignAlg c) ≋? proj₂ (X509.Cert.getCertSignAlg c)
... | no ¬p = no (λ { refl → contradiction (Aeres.Grammar.Definitions.mk≋ refl refl) ¬p})
... | yes (Aeres.Grammar.Definitions.mk≋ refl refl) = yes refl


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

SCP4 : ∀ {@0 bs} → X509.Cert bs → Set
SCP4 c = ℤ.+ 0  ℤ.<  X509.Cert.getSerial c

scp4 : ∀ {@0 bs} (c : X509.Cert bs) → Dec (SCP4 c)
scp4 c = (ℤ.+ 0  ℤ.<?  X509.Cert.getSerial c)





