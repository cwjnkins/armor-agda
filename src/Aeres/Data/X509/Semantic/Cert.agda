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
-- TODO : fix the parser to enforce set length to minimum 1
SCP5 : ∀ {@0 bs} → X509.Cert bs → Set
SCP5 c = 0 < X509.Cert.getIssuerLen c 

scp5 : ∀ {@0 bs} (c : X509.Cert bs) → Dec (SCP5 c)
scp5 c = 0 <? X509.Cert.getIssuerLen c 


-- is it a CA certificate? the Basic Constraints extension is present and the value of CA is TRUE ?
isCA : Exists─ (List Dig) (Option (X509.ExtensionFields (_≡ X509.ExtensionOID.BC) X509.BCFields)) → Bool
isCA (─ .[] , Aeres.Grammar.Definitions.none) = false
isCA (fst , Aeres.Grammar.Definitions.some (X509.mkExtensionFields extnId extnId≡ crit (Generic.mkTLV len (Generic.mkTLV len₁ (X509.mkBCFieldsSeqFields Aeres.Grammar.Definitions.none bcpathlen bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isCA (fst , Aeres.Grammar.Definitions.some (X509.mkExtensionFields extnId extnId≡ crit (Generic.mkTLV len (Generic.mkTLV len₁ (X509.mkBCFieldsSeqFields (Aeres.Grammar.Definitions.some (Generic.mkTLV len₂ (Generic.mkBoolValue v b vᵣ bs≡₅) len≡₂ bs≡₄)) bcpathlen bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = v


-- If the Subject is a CA (e.g., the Basic Constraints extension, is present and the value of CA is TRUE),
-- then the Subject field MUST be populated with a non-empty distinguished name.
SCP6 : ∀ {@0 bs} → X509.Cert bs → Set
SCP6 c = T (isCA (X509.Cert.getBC c)) → (0 < X509.Cert.getSubjectLen c)

scp6 : ∀ {@0 bs} (c : X509.Cert bs) → Dec (SCP6 c)
scp6 c
  with isCA (X509.Cert.getBC c)
... | false = yes (λ ())
... | true
  with 0 <? X509.Cert.getSubjectLen c
... | no ¬p = no λ x → contradiction (x tt) ¬p
... | yes p = yes (λ _ → p)


-- Unique Identifiers fields MUST only appear if the Version is 2 or 3.
SCP7₁ : ∀ {@0 bs} → X509.Cert bs → Set
SCP7₁ c = T (isSome (proj₂ (X509.Cert.getSubUID c))) → (X509.Cert.getVersion c ≡ ℤ.+ 1 ⊎ X509.Cert.getVersion c ≡  ℤ.+ 2)

SCP7₂ : ∀ {@0 bs} → X509.Cert bs → Set
SCP7₂ c = T (isSome (proj₂ (X509.Cert.getIssUID c))) → (X509.Cert.getVersion c ≡ ℤ.+ 1 ⊎ X509.Cert.getVersion c ≡  ℤ.+ 2)

scp7₁ : ∀ {@0 bs} (c : X509.Cert bs) → Dec (SCP7₁ c)
scp7₁ c
  with isSome (proj₂ (X509.Cert.getSubUID c))
... | false = yes (λ ())
... | true
  with X509.Cert.getVersion c
... | v
  with (v ≟ ℤ.+ 1 ⊎-dec v ≟ ℤ.+ 2)
... | yes v≡ = yes (λ _ → v≡)
... | no ¬v≡ = no (λ x → contradiction (x tt) ¬v≡)

scp7₂ : ∀ {@0 bs} (c : X509.Cert bs) → Dec (SCP7₂ c)
scp7₂ c
  with isSome (proj₂ (X509.Cert.getIssUID c))
... | false = yes (λ ())
... | true
  with X509.Cert.getVersion c
... | v
  with (v ≟ ℤ.+ 1 ⊎-dec v ≟ ℤ.+ 2)
... | yes v≡ = yes (λ _ → v≡)
... | no ¬v≡ = no (λ x → contradiction (x tt) ¬v≡)
 
