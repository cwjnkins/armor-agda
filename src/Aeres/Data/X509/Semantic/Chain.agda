{-# OPTIONS --sized-types #-}

import      Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Semantic.StringPrep.ExecDS
open import Aeres.Data.X509.Semantic.StringPrep.ExecPS
open import Aeres.Data.X509.Semantic.StringPrep.ExecIS
open import Aeres.Data.X509.Semantic.Cert
open import Aeres.Data.X509.Semantic.Cert.Utils
import      Aeres.Grammar.Definitions
open import Aeres.Grammar.IList as IList
import      Aeres.Grammar.Option
import      Aeres.Grammar.Parallel
open import Aeres.Prelude
import      Aeres.Data.X509.Semantic.Chain.Builder as Chain
open import Aeres.Data.X509.Semantic.Chain.NameMatch

open import  Aeres.Data.X509.Name.RDN.ATV.OIDs

module Aeres.Data.X509.Semantic.Chain where

open Aeres.Binary
open Chain hiding (toList)
open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8
open Aeres.Grammar.Parallel    UInt8


------- helper functions ------

CCP10Seq : List (Exists─ (List UInt8) Cert) → Set
CCP10Seq [] = ⊥
CCP10Seq ((fst , snd) ∷ []) = ⊤
CCP10Seq ((fst , snd) ∷ (fst₁ , snd₁) ∷ x₁) = T(isCA (Cert.getBC snd₁)) × CCP10Seq ((fst₁ , snd₁) ∷ x₁)

helperCCP4₁-h : ∀ {@0 h t} → Extension.CRLDistPoint.DistPoint h → IList UInt8 Extension.CRLDistPoint.DistPoint t  → Set
helperCCP4₁-h (mkTLV len (Extension.CRLDistPoint.mkDistPointFields crldp crldprsn none bs≡₁) len≡ bs≡) x₁ = ⊥
helperCCP4₁-h (mkTLV len (Extension.CRLDistPoint.mkDistPointFields crldp crldprsn (some x) bs≡₁) len≡ bs≡) nil = ⊤ 
helperCCP4₁-h (mkTLV len (Extension.CRLDistPoint.mkDistPointFields crldp crldprsn (some x) bs≡₁) len≡ bs≡) (cons (mkIListCons head₁ tail₁ bs≡₂)) = helperCCP4₁-h head₁ tail₁
  
helperCCP4₁ : Exists─ (List UInt8) (Option ExtensionFieldCRLDist) → Set
helperCCP4₁ (─ .[] , none) = ⊤
helperCCP4₁ (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mk×ₚ (cons (mkIListCons head₁ tail₁ bs≡₄)) snd₁) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = helperCCP4₁-h head₁ tail₁

helperCCP4₂-h : ∀ {@0 h t} → Extension.CRLDistPoint.DistPoint h → IList UInt8 Extension.CRLDistPoint.DistPoint t  → Set
helperCCP4₂-h (mkTLV len (Extension.CRLDistPoint.mkDistPointFields none crldprsn none bs≡₁) len≡ bs≡) x₁ = ⊥
helperCCP4₂-h (mkTLV len (Extension.CRLDistPoint.mkDistPointFields none crldprsn (some x) bs≡₁) len≡ bs≡) x₁ = ⊥
helperCCP4₂-h (mkTLV len (Extension.CRLDistPoint.mkDistPointFields (some x) crldprsn none bs≡₁) len≡ bs≡) nil = ⊤
helperCCP4₂-h (mkTLV len (Extension.CRLDistPoint.mkDistPointFields (some x) crldprsn none bs≡₁) len≡ bs≡) (cons (mkIListCons head₁ tail₁ bs≡₂)) = helperCCP4₂-h head₁ tail₁
helperCCP4₂-h (mkTLV len (Extension.CRLDistPoint.mkDistPointFields (some x) crldprsn (some y) bs≡₁) len≡ bs≡) x₁ = ⊥

helperCCP4₂ : Exists─ (List UInt8) (Option ExtensionFieldCRLDist) → Set
helperCCP4₂ (─ .[] , none) = ⊤
helperCCP4₂ (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mk×ₚ (cons (mkIListCons head₁ tail₁ bs≡₄)) snd₁) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = helperCCP4₂-h head₁ tail₁

helperCCP4 : (c : List (Exists─ (List UInt8) Cert)) → Set
helperCCP4 [] = ⊥
helperCCP4 (x₁ ∷ []) = ⊤
helperCCP4 (x₁ ∷ x₂ ∷ t) with helperCCP4 (x₂ ∷ t) | isCRLSignPresent (Cert.getKU (proj₂ x₂))
... | rec | true =  helperCCP4₂ (Cert.getCRLDIST (proj₂ x₁)) × rec
... | rec | false = helperCCP4₁ (Cert.getCRLDIST (proj₂ x₁)) × rec


helperCCP4₂-h-dec : ∀ {@0 h t} → (a : Extension.CRLDistPoint.DistPoint h) → (b : IList UInt8 Extension.CRLDistPoint.DistPoint t)  → Dec (helperCCP4₂-h a b)
helperCCP4₂-h-dec (mkTLV len (Extension.CRLDistPoint.mkDistPointFields none crldprsn none bs≡₁) len≡ bs≡) x₁ = no (λ())
helperCCP4₂-h-dec (mkTLV len (Extension.CRLDistPoint.mkDistPointFields none crldprsn (some x) bs≡₁) len≡ bs≡) x₁ = no (λ())
helperCCP4₂-h-dec (mkTLV len (Extension.CRLDistPoint.mkDistPointFields (some x) crldprsn none bs≡₁) len≡ bs≡) nil = yes tt
helperCCP4₂-h-dec (mkTLV len (Extension.CRLDistPoint.mkDistPointFields (some x) crldprsn none bs≡₁) len≡ bs≡) (cons (mkIListCons head₁ tail₁ bs≡₂)) = helperCCP4₂-h-dec head₁ tail₁
helperCCP4₂-h-dec (mkTLV len (Extension.CRLDistPoint.mkDistPointFields (some x) crldprsn (some y) bs≡₁) len≡ bs≡) x₁ = no (λ())

helperCCP4₂-dec : (c : Exists─ (List UInt8) (Option ExtensionFieldCRLDist)) → Dec (helperCCP4₂ c)
helperCCP4₂-dec (─ .[] , none) = yes tt
helperCCP4₂-dec (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mk×ₚ (cons (mkIListCons head₁ tail₁ bs≡₄)) snd₁) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = helperCCP4₂-h-dec head₁ tail₁

helperCCP4₁-h-dec : ∀ {@0 h t} → (a : Extension.CRLDistPoint.DistPoint h) → (b : IList UInt8 Extension.CRLDistPoint.DistPoint t)  → Dec (helperCCP4₁-h a b)
helperCCP4₁-h-dec (mkTLV len (Extension.CRLDistPoint.mkDistPointFields crldp crldprsn none bs≡₁) len≡ bs≡) x₁ = no (λ())
helperCCP4₁-h-dec (mkTLV len (Extension.CRLDistPoint.mkDistPointFields crldp crldprsn (some x) bs≡₁) len≡ bs≡) nil = yes tt 
helperCCP4₁-h-dec (mkTLV len (Extension.CRLDistPoint.mkDistPointFields crldp crldprsn (some x) bs≡₁) len≡ bs≡) (cons (mkIListCons head₁ tail₁ bs≡₂)) = helperCCP4₁-h-dec head₁ tail₁

helperCCP4₁-dec : (c : Exists─ (List UInt8) (Option ExtensionFieldCRLDist)) → Dec (helperCCP4₁ c)
helperCCP4₁-dec (─ .[] , none) = yes tt
helperCCP4₁-dec (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mk×ₚ (cons (mkIListCons head₁ tail₁ bs≡₄)) snd₁) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = helperCCP4₁-h-dec head₁ tail₁

helperCCP4-dec : (c : List (Exists─ (List UInt8) Cert)) → Dec (helperCCP4 c)
helperCCP4-dec [] = no λ()
helperCCP4-dec (x₁ ∷ []) = yes tt
helperCCP4-dec (x₁ ∷ x₂ ∷ t) with helperCCP4-dec (x₂ ∷ t) | isCRLSignPresent (Cert.getKU (proj₂ x₂))
... | rec | true = helperCCP4₂-dec (Cert.getCRLDIST (proj₂ x₁)) ×-dec rec
... | rec | false = helperCCP4₁-dec (Cert.getCRLDIST (proj₂ x₁)) ×-dec rec

------------------------------------------------------------------------

countNextIntCACerts : List (Exists─ (List UInt8) Cert) → ℤ → ℤ
countNextIntCACerts [] n = n
countNextIntCACerts ((fst , snd) ∷ x₁) n
  with isCA (Cert.getBC snd)
... | false = countNextIntCACerts x₁ n
... | true
  with nameMatch? (Cert.getIssuer snd) (Cert.getSubject snd)
... | no ¬p =  countNextIntCACerts x₁ (n ℤ.+ ℤ.+ 1) 
... | yes p =  countNextIntCACerts x₁ n

helperCCP3 : Exists─ (List UInt8) Cert → List (Exists─ (List UInt8) Cert) → Set
helperCCP3 (fst , snd) x₁
  with isCA (Cert.getBC snd) ∧ isKeyCertSignPresent (Cert.getKU snd)
... | false = ⊤
... | true
  with (getBCPathLen (Cert.getBC snd))
... | (─ .[] , none) = ⊤
... | (fst , some x) = countNextIntCACerts x₁ (ℤ.+ 0) ℤ.≤ Int.getVal x

CCP3Seq : List (Exists─ (List UInt8) Cert) → Set
CCP3Seq [] = ⊤
CCP3Seq (x ∷ x₁) =  helperCCP3 x x₁ × CCP3Seq x₁

helperCCP3-dec : (c : Exists─ (List UInt8) Cert) → (t : List (Exists─ (List UInt8) Cert)) → Dec (helperCCP3 c t)
helperCCP3-dec (fst , snd) x₁
  with isCA (Cert.getBC snd) ∧ isKeyCertSignPresent (Cert.getKU snd)
... | false = yes tt
... | true
  with (getBCPathLen (Cert.getBC snd))
... | (─ .[] , none) = yes tt
... | (fst , some x) = countNextIntCACerts x₁ (ℤ.+ 0) ℤ.≤? Int.getVal x
-------------------------- CCP rules ---------------------------------------

-- https://datatracker.ietf.org/doc/html/rfc5280#section-6.1.4 (k)
-- Conforming implementations may choose to reject all Version 1 and Version 2 intermediate CA certificates

CCP2 : ∀ {@0 bs} {trustedRoot candidates : List (Exists─ _ Cert)} (issuee : Cert bs)
  → Chain trustedRoot candidates issuee → Set
CCP2 issuee (root x) = Cert.getVersion issuee ≡ TBSCert.v3
CCP2 issuee (link issuer isIn x) = Cert.getVersion issuee ≡ TBSCert.v3 × CCP2 issuer x

ccp2 : ∀ {@0 bs} {trustedRoot candidates : List (Exists─ _ Cert)} (issuee : Cert bs)
  → (c : Chain trustedRoot candidates issuee) → Dec (CCP2 issuee c)
ccp2 issuee (root x) = Cert.getVersion issuee ≟ TBSCert.v3
ccp2 issuee (link issuer isIn x) = Cert.getVersion issuee ≟ TBSCert.v3 ×-dec ccp2 issuer x


-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.2.1.9
-- The PathLenConstraint field is meaningful only if the CA boolean
-- is asserted and the Key Usage extension, if present, asserts the KeyCertSign bit. In this case, it gives
-- the maximum number of non-self-issued intermediate certificates that may follow this certificate in a valid certification path.

CCP3 : ∀ {@0 bs} {trustedRoot candidates : List (Exists─ _ Cert)} (issuee : Cert bs)
  → Chain trustedRoot candidates issuee → Set
CCP3 issuee c = CCP3Seq (reverse (Chain.toList c))

ccp3 : ∀ {@0 bs} {trustedRoot candidates : List (Exists─ _ Cert)} (issuee : Cert bs)
  → (c : Chain trustedRoot candidates issuee) → Dec (CCP3 issuee c)
ccp3 issuee c = CCP3Seq-dec (reverse (Chain.toList c))
  where
  CCP3Seq-dec : (c : List (Exists─ (List UInt8) Cert)) → Dec (CCP3Seq c)
  CCP3Seq-dec [] = yes tt
  CCP3Seq-dec (x ∷ x₁) = helperCCP3-dec x x₁ ×-dec CCP3Seq-dec x₁

-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.2.1.13
-- For DistributionPoint field, if the certificate issuer is not the CRL issuer,
-- then the CRLIssuer field MUST be present and contain the Name of the CRL issuer. If the
-- certificate issuer is also the CRL issuer, then conforming CAs MUST omit the CRLIssuer
-- field and MUST include the distributionPoint field.

CCP4 : ∀ {@0 bs} {trustedRoot candidates : List (Exists─ _ Cert)} (issuee : Cert bs)
  → Chain trustedRoot candidates issuee → Set
CCP4 issuee c = helperCCP4 (Chain.toList c)

ccp4 : ∀ {@0 bs} {trustedRoot candidates : List (Exists─ _ Cert)} (issuee : Cert bs)
  → (c : Chain trustedRoot candidates issuee) → Dec (CCP4 issuee c)
ccp4 issuee c = helperCCP4-dec (Chain.toList c)

-- https://datatracker.ietf.org/doc/html/rfc5280#section-6.1
-- A certificate MUST NOT appear more than once in a prospective certification path.

CCP5 : ∀ {@0 bs} {trustedRoot candidates : List (Exists─ _ Cert)} (issuee : Cert bs)
  → Chain trustedRoot candidates issuee → Set
CCP5 issuee c = List.Unique _≟_ (Chain.toList c)

ccp5 : ∀ {@0 bs} {trustedRoot candidates : List (Exists─ _ Cert)} (issuee : Cert bs)
  → (c : Chain trustedRoot candidates issuee) → Dec (CCP5 issuee c)
ccp5 issuee c = List.unique? _≟_ (Chain.toList c)

-- -- https://datatracker.ietf.org/doc/html/rfc5280#section-4.1.2.4
-- -- Certificate users MUST be prepared to process the Issuer distinguished name
-- -- and Subject distinguished name fields to perform name chaining for certification path validation.

-- CCP6 : ∀ {@0 bs} → CertList bs → Set
-- CCP6 c = CCP6Seq (chainToList c)

-- ccp6 : ∀ {@0 bs} (c : CertList bs) → Dec (CCP6 c)
-- ccp6 c = helper (chainToList c)
--   where
--   helper : (c : List (Exists─ (List UInt8) Cert)) → Dec (CCP6Seq c)
--   helper [] = no (λ ())
--   helper ((fst , snd) ∷ []) = yes tt
--   helper ((fst , snd) ∷ (fst₁ , snd₁) ∷ x₂) = (MatchRDNSeq-dec (Cert.getIssuer snd) (Cert.getSubject snd₁)) ×-dec helper ((fst₁ , snd₁) ∷ x₂)

-- https://datatracker.ietf.org/doc/html/rfc5280#section-6
--- check whether any of the certificate in given chain is trusted by the system's trust anchor

-- CCP7 :∀ {@0 bs} {trustedRoot candidates : List (Exists─ _ Cert)} (issuee : Cert bs)
--   → Chain trustedRoot candidates issuee → Set
-- CCP7 r c = helperCCP7 (chainToList r) (chainToList c)

-- ccp7 :∀ {@0 bs} {trustedRoot candidates : List (Exists─ _ Cert)} (issuee : Cert bs)
--   → (c : Chain trustedRoot candidates issuee) → Dec (CCP7 issuee c)
-- ccp7 r c = helperCCP7-dec (chainToList r) (chainToList c)

-- https://datatracker.ietf.org/doc/html/rfc5280#section-6
--- every issuer certificate in a chain must be CA certificate

CCP10 : ∀ {@0 bs} {trustedRoot candidates : List (Exists─ _ Cert)} (issuee : Cert bs)
  → Chain trustedRoot candidates issuee → Set
CCP10 issuee c = CCP10Seq (Chain.toList c)

ccp10 : ∀ {@0 bs} {trustedRoot candidates : List (Exists─ _ Cert)} (issuee : Cert bs)
  → (c : Chain trustedRoot candidates issuee) → Dec (CCP10 issuee c)
ccp10 issuee c = helper (Chain.toList c)
  where
  helper : (c : List (Exists─ (List UInt8) Cert)) → Dec (CCP10Seq c)
  helper [] = no λ()
  helper ((fst , snd) ∷ []) = yes tt
  helper ((fst , snd) ∷ (fst₁ , snd₁) ∷ t) = T-dec ×-dec helper ((fst₁ , snd₁) ∷ t)
