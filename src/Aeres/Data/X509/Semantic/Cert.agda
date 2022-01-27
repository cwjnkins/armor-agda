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

-- SignatureAlgorithm field MUST contain the same algorithm identifier as
-- the Signature field in the sequence TbsCertificate.
SCP1 : ∀ {@0 bs} → X509.Cert bs → Set
SCP1 c = X509.Cert.getTBSCertSignAlg c ≡ X509.Cert.getCertSignAlg c

scp1 :  ∀ {@0 bs} (c : X509.Cert bs) → Dec (SCP1 c)
scp1 c
  with proj₂ (X509.Cert.getTBSCertSignAlg c) ≋? proj₂ (X509.Cert.getCertSignAlg c)
... | no ¬p = no (λ { refl → contradiction (Aeres.Grammar.Definitions.mk≋ refl refl) ¬p})
... | yes (Aeres.Grammar.Definitions.mk≋ refl refl) = yes refl


-- Extension field MUST only appear if the Version is 3(2).
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


-- At a minimum, conforming implementations MUST recognize Version 3 certificates.
-- Generation of Version 2 certificates is not expected by implementations based on this profile.
-- note : but, version 1 and 2 certs can be present for CA certificates. So, we are checking whether
-- the version is 1, 2, or 3 (0 - 2).
SCP3 : ∀ {@0 bs} → X509.Cert bs → Set
SCP3 c = ((X509.Cert.getVersion c ≡ ℤ.+ 0) ⊎ (X509.Cert.getVersion c ≡  ℤ.+ 1)) ⊎ (X509.Cert.getVersion c ≡  ℤ.+ 2)

scp3 : ∀ {@0 bs} (c : X509.Cert bs) → Dec (SCP3 c)
scp3 c = ((X509.Cert.getVersion c ≟ ℤ.+ 0) ⊎-dec (X509.Cert.getVersion c ≟  ℤ.+ 1)) ⊎-dec (X509.Cert.getVersion c ≟  ℤ.+ 2)


-- The Serial number MUST be a positive integer assigned by the CA to each certificate.
SCP4 : ∀ {@0 bs} → X509.Cert bs → Set
SCP4 c = ℤ.+ 0 ℤ.< X509.Cert.getSerial c

scp4 : ∀ {@0 bs} (c : X509.Cert bs) → Dec (SCP4 c)
scp4 c = (ℤ.+ 0 ℤ.<? X509.Cert.getSerial c)


-- The Issuer field MUST contain a non-empty distinguished name (DN).
SCP5 : ∀ {@0 bs} → X509.Cert bs → Set
SCP5 c = 0 < X509.Cert.getIssuerLen c 

scp5 : ∀ {@0 bs} (c : X509.Cert bs) → Dec (SCP5 c)
scp5 c = 0 <? X509.Cert.getIssuerLen c 

