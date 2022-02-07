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


------- helper functions -----
-- is it a CA certificate? the Basic Constraints extension is present and the value of CA is TRUE ?
isCA : Exists─ (List Dig) (Option (X509.ExtensionFields (_≡ X509.ExtensionOID.BC) X509.BCFields)) → Bool
isCA (─ .[] , Aeres.Grammar.Definitions.none) = false
isCA (fst , Aeres.Grammar.Definitions.some (X509.mkExtensionFields extnId extnId≡ crit (Generic.mkTLV len (Generic.mkTLV len₁ (X509.mkBCFieldsSeqFields Aeres.Grammar.Definitions.none bcpathlen bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isCA (fst , Aeres.Grammar.Definitions.some (X509.mkExtensionFields extnId extnId≡ crit (Generic.mkTLV len (Generic.mkTLV len₁ (X509.mkBCFieldsSeqFields (Aeres.Grammar.Definitions.some (Generic.mkTLV len₂ (Generic.mkBoolValue v b vᵣ bs≡₅) len≡₂ bs≡₄)) bcpathlen bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = v


-- returns BCPathLen if exists
getBCPathLen : Exists─ (List Dig) (Option (X509.ExtensionFields (_≡ X509.ExtensionOID.BC) X509.BCFields)) → Exists─ (List Dig) (Option Generic.Int)
getBCPathLen (─ .[] , Aeres.Grammar.Definitions.none) = _ , none
getBCPathLen (fst , Aeres.Grammar.Definitions.some (X509.mkExtensionFields extnId extnId≡ crit (Generic.mkTLV len (Generic.mkTLV len₁ (X509.mkBCFieldsSeqFields bcca bcpathlen bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = _ , bcpathlen


-- isCRLSign present in KU extension ? bit 6 == true ?
isCRLIssuer : Exists─ (List Dig) (Option (X509.ExtensionFields (_≡ X509.ExtensionOID.KU) X509.KUFields)) → Bool
isCRLIssuer (─ .[] , Aeres.Grammar.Definitions.none) = false
isCRLIssuer (fst , Aeres.Grammar.Definitions.some (X509.mkExtensionFields extnId extnId≡ crit (Generic.mkTLV len (Generic.mkTLV len₁ (Generic.mkBitstringValue bₕ bₜ bₕ<8 (singleton [] x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isCRLIssuer (fst , Aeres.Grammar.Definitions.some (X509.mkExtensionFields extnId extnId≡ crit (Generic.mkTLV len (Generic.mkTLV len₁ (Generic.mkBitstringValue bₕ bₜ bₕ<8 (singleton (x ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isCRLIssuer (fst , Aeres.Grammar.Definitions.some (X509.mkExtensionFields extnId extnId≡ crit (Generic.mkTLV len (Generic.mkTLV len₁ (Generic.mkBitstringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isCRLIssuer (fst , Aeres.Grammar.Definitions.some (X509.mkExtensionFields extnId extnId≡ crit (Generic.mkTLV len (Generic.mkTLV len₁ (Generic.mkBitstringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isCRLIssuer (fst , Aeres.Grammar.Definitions.some (X509.mkExtensionFields extnId extnId≡ crit (Generic.mkTLV len (Generic.mkTLV len₁ (Generic.mkBitstringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isCRLIssuer (fst , Aeres.Grammar.Definitions.some (X509.mkExtensionFields extnId extnId≡ crit (Generic.mkTLV len (Generic.mkTLV len₁ (Generic.mkBitstringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isCRLIssuer (fst , Aeres.Grammar.Definitions.some (X509.mkExtensionFields extnId extnId≡ crit (Generic.mkTLV len (Generic.mkTLV len₁ (Generic.mkBitstringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isCRLIssuer (fst , Aeres.Grammar.Definitions.some (X509.mkExtensionFields extnId extnId≡ crit (Generic.mkTLV len (Generic.mkTLV len₁ (Generic.mkBitstringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ x₆ ∷ x₇) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = x₆


-- isKeyCertSign present in KU extension ? bit 5 == true ?
isKeyCertSignPresent : Exists─ (List Dig) (Option (X509.ExtensionFields (_≡ X509.ExtensionOID.KU) X509.KUFields)) → Bool
isKeyCertSignPresent (─ .[] , Aeres.Grammar.Definitions.none) = false
isKeyCertSignPresent (fst , Aeres.Grammar.Definitions.some (X509.mkExtensionFields extnId extnId≡ crit (Generic.mkTLV len (Generic.mkTLV len₁ (Generic.mkBitstringValue bₕ bₜ bₕ<8 (singleton [] x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isKeyCertSignPresent (fst , Aeres.Grammar.Definitions.some (X509.mkExtensionFields extnId extnId≡ crit (Generic.mkTLV len (Generic.mkTLV len₁ (Generic.mkBitstringValue bₕ bₜ bₕ<8 (singleton (x ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isKeyCertSignPresent (fst , Aeres.Grammar.Definitions.some (X509.mkExtensionFields extnId extnId≡ crit (Generic.mkTLV len (Generic.mkTLV len₁ (Generic.mkBitstringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isKeyCertSignPresent (fst , Aeres.Grammar.Definitions.some (X509.mkExtensionFields extnId extnId≡ crit (Generic.mkTLV len (Generic.mkTLV len₁ (Generic.mkBitstringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isKeyCertSignPresent (fst , Aeres.Grammar.Definitions.some (X509.mkExtensionFields extnId extnId≡ crit (Generic.mkTLV len (Generic.mkTLV len₁ (Generic.mkBitstringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isKeyCertSignPresent (fst , Aeres.Grammar.Definitions.some (X509.mkExtensionFields extnId extnId≡ crit (Generic.mkTLV len (Generic.mkTLV len₁ (Generic.mkBitstringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isKeyCertSignPresent (fst , Aeres.Grammar.Definitions.some (X509.mkExtensionFields extnId extnId≡ crit (Generic.mkTLV len (Generic.mkTLV len₁ (Generic.mkBitstringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ x₆) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = x₅


-- get KU Bits in bool list
getKUBits : Exists─ (List Dig) (Option (X509.ExtensionFields (_≡ X509.ExtensionOID.KU) X509.KUFields)) → List Bool
getKUBits (─ .[] , Aeres.Grammar.Definitions.none) = []
getKUBits (fst , Aeres.Grammar.Definitions.some (X509.mkExtensionFields extnId extnId≡ crit (Generic.mkTLV len (Generic.mkTLV len₁ (Generic.mkBitstringValue bₕ bₜ bₕ<8 (singleton x x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = x


-- is SAN extension critical ? 
isSANCritical : Exists─ (List Dig) (Option (X509.ExtensionFields (_≡ X509.ExtensionOID.SAN) X509.SANFields)) → Bool
isSANCritical (─ .[] , Aeres.Grammar.Definitions.none) = false
isSANCritical (fst , Aeres.Grammar.Definitions.some (X509.mkExtensionFields extnId extnId≡ Aeres.Grammar.Definitions.none extension bs≡)) = false
isSANCritical (fst , Aeres.Grammar.Definitions.some (X509.mkExtensionFields extnId extnId≡ (Aeres.Grammar.Definitions.some (Generic.mkTLV len (Generic.mkBoolValue v b vᵣ bs≡₂) len≡ bs≡₁)) extension bs≡)) = v


-- get SAN length
getSANLength : Exists─ (List Dig) (Option (X509.ExtensionFields (_≡ X509.ExtensionOID.SAN) X509.SANFields)) → ℕ
getSANLength (─ .[] , Aeres.Grammar.Definitions.none) = 0
getSANLength (fst , Aeres.Grammar.Definitions.some (X509.mkExtensionFields extnId extnId≡ crit (Generic.mkTLV len (Generic.mkTLV len₁ (Aeres.Grammar.Definitions.mk×ₚ fstₚ₁ sndₚ₁ bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = Generic.lengthSequence fstₚ₁


-- is SAN present in Cert ?
isSANPresent : Exists─ (List Dig) (Option (X509.ExtensionFields (_≡ X509.ExtensionOID.SAN) X509.SANFields)) → Bool
isSANPresent (─ .[] , Aeres.Grammar.Definitions.none) = false
isSANPresent (fst , Aeres.Grammar.Definitions.some x) = true


-- returns all certificate policy OIDs
getPolicyOIDList : Exists─ (List Dig) (Option (X509.ExtensionFields (_≡ X509.ExtensionOID.CPOL) X509.CertPolFields)) →  List (Exists─ (List Dig) Generic.OID)
getPolicyOIDList (─ .[] , Aeres.Grammar.Definitions.none) = []
getPolicyOIDList (fst , Aeres.Grammar.Definitions.some (X509.mkExtensionFields extnId extnId≡ crit (Generic.mkTLV len (Generic.mkTLV len₁ val len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = helper val
  where
  helper : ∀ {@0 bs} → Generic.SequenceOf X509.PolicyInformation bs → List (Exists─ (List Dig) Generic.OID)
  helper Generic.nil = []
  helper (Generic.cons (Generic.mkSequenceOf (Generic.mkTLV len (X509.mkPolicyInformationFields cpid cpqls bs≡₂) len≡ bs≡₁) t bs≡)) = (_ , cpid) ∷ (helper t)


-- returns true only if the extension is unknown and has critical bit = true
isUnkwnCriticalExtension : Exists─ (List Dig) X509.Extension → Bool
isUnkwnCriticalExtension (fst , Generic.mkTLV len (X509.other (X509.mkExtensionFields extnId extnId≡ Aeres.Grammar.Definitions.none extension bs≡₁)) len≡ bs≡) = false
isUnkwnCriticalExtension (fst , Generic.mkTLV len (X509.other (X509.mkExtensionFields extnId extnId≡ (Aeres.Grammar.Definitions.some (Generic.mkTLV len₁ (Generic.mkBoolValue v b vᵣ bs≡₃) len≡₁ bs≡₂)) extension bs≡₁)) len≡ bs≡) = v
isUnkwnCriticalExtension (fst , Generic.mkTLV len _ len≡ bs≡) = false

-- is any unknown extention critical from the list ?
isAnyOtherExtnCritical : List (Exists─ (List Dig) X509.Extension) → Bool
isAnyOtherExtnCritical x = helper x
  where
  -- returns true only if at least one extension in the list is unknown and that extension has critical bit = true
  helper : List (Exists─ (List Dig) X509.Extension) → Bool
  helper [] = false
  helper (x ∷ x₁) = case (isUnkwnCriticalExtension x) of λ where
    false → helper x₁
    true → true


getExtensionsOIDList : List (Exists─ (List Dig) X509.Extension) →  List (Exists─ (List Dig) Generic.OID)
getExtensionsOIDList = map helper
  where
  helper : Exists─ (List Dig) X509.Extension → (Exists─ (List Dig) Generic.OID)
  helper (fst , Generic.mkTLV len (X509.akiextn x) len≡ bs≡) = _ , (X509.ExtensionFields.extnId x)
  helper (fst , Generic.mkTLV len (X509.skiextn x) len≡ bs≡) = _ , (X509.ExtensionFields.extnId x)
  helper (fst , Generic.mkTLV len (X509.kuextn x) len≡ bs≡) = _ , (X509.ExtensionFields.extnId x)
  helper (fst , Generic.mkTLV len (X509.ekuextn x) len≡ bs≡) = _ , (X509.ExtensionFields.extnId x)
  helper (fst , Generic.mkTLV len (X509.bcextn x) len≡ bs≡) = _ , (X509.ExtensionFields.extnId x)
  helper (fst , Generic.mkTLV len (X509.ianextn x) len≡ bs≡) = _ , (X509.ExtensionFields.extnId x)
  helper (fst , Generic.mkTLV len (X509.sanextn x) len≡ bs≡) = _ , (X509.ExtensionFields.extnId x)
  helper (fst , Generic.mkTLV len (X509.cpextn x) len≡ bs≡) = _ , (X509.ExtensionFields.extnId x)
  helper (fst , Generic.mkTLV len (X509.crlextn x) len≡ bs≡) = _ , (X509.ExtensionFields.extnId x)
  helper (fst , Generic.mkTLV len (X509.aiaextn x) len≡ bs≡) = _ , (X509.ExtensionFields.extnId x)
  helper (fst , Generic.mkTLV len (X509.other x) len≡ bs≡) = _ , (X509.ExtensionFields.extnId x)


-- checkCRLDist : Exists─ (List Dig) (Option (X509.ExtensionFields (_≡ X509.ExtensionOID.CRLDIST) X509.CRLDistFields)) → Bool
-- checkCRLDist (─ .[] , Aeres.Grammar.Definitions.none) = true
-- checkCRLDist (fst , Aeres.Grammar.Definitions.some (X509.mkExtensionFields extnId extnId≡ crit (Generic.mkTLV len (Generic.mkTLV len₁ (Aeres.Grammar.Definitions.mk×ₚ (Generic.cons (Generic.mkSequenceOf (Generic.mkTLV len₂ val len≡₂ bs≡₅) t bs≡₄)) sndₚ₁ bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = {!!}


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


-- Where it appears, the PathLenConstraint field MUST be greater than or equal to zero.
SCP8 : ∀ {@0 bs} → X509.Cert bs → Set
SCP8 c
  with getBCPathLen (X509.Cert.getBC c)
... | ─ .[] , Aeres.Grammar.Definitions.none = (T true)
... | fst , Aeres.Grammar.Definitions.some x = (ℤ.+ 0 ℤ.≤ Generic.Int.getVal x)

scp8 : ∀ {@0 bs} (c : X509.Cert bs) → Dec (SCP8 c)
scp8 c
  with getBCPathLen (X509.Cert.getBC c)
... | ─ .[] , Aeres.Grammar.Definitions.none = yes tt
... | fst , Aeres.Grammar.Definitions.some x = (ℤ.+ 0 ℤ.≤? Generic.Int.getVal x)


-- if the Subject is a CRL issuer (e.g., the Key Usage extension, is present and the value of CRLSign is TRUE),
-- then the Subject field MUST be populated with a non-empty distinguished name.
SCP9 : ∀ {@0 bs} → X509.Cert bs → Set
SCP9 c = T (isCRLIssuer (X509.Cert.getKU c)) → (0 < X509.Cert.getSubjectLen c)

scp9 : ∀ {@0 bs} (c : X509.Cert bs) → Dec (SCP9 c)
scp9 c
  with (isCRLIssuer (X509.Cert.getKU c))
... | false = yes (λ ())
... | true
  with (0 <? X509.Cert.getSubjectLen c)
... | no ¬p = no λ x → contradiction (x tt) ¬p
... | yes p = yes (λ x → p)


-- When the Key Usage extension appears in a certificate, at least one of the bits MUST be set to 1.
SCP10 : ∀ {@0 bs} → X509.Cert bs → Set
SCP10 c = true ∈ getKUBits (X509.Cert.getKU c)

scp10 : ∀ {@0 bs} (c : X509.Cert bs) → Dec (SCP10 c)
scp10 c = true ∈? getKUBits (X509.Cert.getKU c)


-- If subject naming information is present only in the Subject Alternative Name extension ,
-- then the Subject name MUST be an empty sequence and the Subject Alternative Name extension MUST be critical.
-- If the subject field contains an empty sequence, then the issuing CA MUST include a
-- subjectAltName extension that is marked as critical.
SCP11 : ∀ {@0 bs} → X509.Cert bs → Set
SCP11 c = (0 ≡ X509.Cert.getSubjectLen c) → T (isSANCritical (X509.Cert.getSAN c))

scp11 : ∀ {@0 bs} (c : X509.Cert bs) → Dec (SCP11 c)
scp11 c with (0 ≟ X509.Cert.getSubjectLen c)
scp11 c    | no n with isSANCritical (X509.Cert.getSAN c)
scp11 c    | no n    | false = yes n
scp11 c    | no n    | true  = yes (λ x → tt)
scp11 c    | yes y with isSANCritical (X509.Cert.getSAN c)
scp11 c    | yes y   | false = no (λ x → contradiction y x)
scp11 c    | yes y   | true  = yes (λ x → tt)


-- If the Subject Alternative Name extension is present, the sequence MUST contain at least one entry.
SCP12 : ∀ {@0 bs} → X509.Cert bs → Set
SCP12 c = T (isSANPresent (X509.Cert.getSAN c)) → (0 < getSANLength (X509.Cert.getSAN c))

scp12 : ∀ {@0 bs} (c : X509.Cert bs) → Dec (SCP12 c)
scp12 c
  with isSANPresent (X509.Cert.getSAN c)
... | false = yes (λ ())
... | true
  with 0 <? getSANLength (X509.Cert.getSAN c)
... | yes y = yes (λ x → y)
... | no n = no (λ x → contradiction (x tt) n)


-- If the KeyCertSign bit is asserted, then the CA bit in the Basic Constraints extension MUST also be asserted.
SCP13 : ∀ {@0 bs} → X509.Cert bs → Set
SCP13 c = T (isKeyCertSignPresent (X509.Cert.getKU c)) → T (isCA (X509.Cert.getBC c))

scp13 : ∀ {@0 bs} (c : X509.Cert bs) → Dec (SCP13 c)
scp13 c with isKeyCertSignPresent (X509.Cert.getKU c)
scp13 c    | false with isCA (X509.Cert.getBC c)
scp13 c    | false    | _ =  yes (λ ())
scp13 c    | true with isCA (X509.Cert.getBC c)
scp13 c    | true     | false = no (contradiction tt)
scp13 c    | true     | true  = yes λ x → x


-- A certificate MUST NOT include more than one instance of a particular Extension.
SCP14 : ∀ {@0 bs} → X509.Cert bs → Set
SCP14 c = List.Unique _≟_ (getExtensionsOIDList (X509.Cert.getExtensionsList c))

scp14 : ∀ {@0 bs} (c : X509.Cert bs) → Dec (SCP14 c)
scp14 c = List.unique? _≟_ (getExtensionsOIDList (X509.Cert.getExtensionsList c))


-- A certificate-using system MUST reject the certificate if it encounters a critical Extension
-- it does not recognize or a critical Extension that contains information that it cannot process.
SCP15 : ∀ {@0 bs} → X509.Cert bs → Set
SCP15 c = T (isAnyOtherExtnCritical (X509.Cert.getExtensionsList c)) → T false

scp15 : ∀ {@0 bs} (c : X509.Cert bs) → Dec (SCP15 c)
scp15 c
  with isAnyOtherExtnCritical (X509.Cert.getExtensionsList c)
... | false = yes (λ ())
... | true = no (contradiction tt)


-- A certificate policy OID MUST NOT appear more than once in a Certificate Policies extension.
SCP16 : ∀ {@0 bs} → X509.Cert bs → Set
SCP16 c = List.Unique _≟_ (getPolicyOIDList (X509.Cert.getCPOL c))

scp16 : ∀ {@0 bs} (c : X509.Cert bs) → Dec (SCP16 c)
scp16 c = List.unique? _≟_ (getPolicyOIDList (X509.Cert.getCPOL c))


-- While each of these fields is optional, a DistributionPoint MUST NOT consist of only the Reasons field;
-- either distributionPoint or CRLIssuer MUST be present.
-- The certificate Validity period includes the current time
