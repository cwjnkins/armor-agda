{-# OPTIONS --erasure --sized-types #-}

open import Armor.Binary
open import Armor.Data.X509
open import Armor.Data.X509.Validity.Time.Ordering
open import Armor.Data.X509.CRL.CertList.TCB as CRL
open import Armor.Data.X509.CRL.Version
open import Armor.Data.X509.CRL.RevokedCertificates
open import Armor.Data.X509.CRL.Semantic.Utils
open import Armor.Data.X509.Semantic.Cert.Utils
open import Armor.Data.X509.Semantic.Chain.TCB
open import Armor.Data.X509.Semantic.Chain.NameMatch
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
import Armor.Grammar.Parallel.TCB
open import Armor.Grammar.IList as IList
open import Armor.Prelude

module Armor.Data.X509.CRL.Semantic.R1 where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8
open Armor.Grammar.Parallel.TCB UInt8

getCRLDecodedVersion : ∀ {@0 bs} → (c : CRL.CertList bs) → DecodedVersion
getCRLDecodedVersion c
  with CRL.CertList.getVersion c
... | none = v1
... | some v = getDecodedVersion v

-- When CRLs are issued, the CRLs MUST be version 2 CRLs
CRLR1 : ∀ {@0 bs} → CRL.CertList bs → Set
CRLR1 c = getCRLDecodedVersion c ≡ v2

CRLr1 : ∀ {@0 bs} → (c : CRL.CertList bs) → Dec (CRLR1 c)
CRLr1 c = getCRLDecodedVersion c ≟ v2


-- Signature Algorithm field MUST contain the same algorithm identifier as the
--   signature field in the sequence tbsCertList
CRLR2 : ∀ {@0 bs} → CRL.CertList bs → Set
CRLR2 c = _≋_{A = SignAlg} (CRL.CertList.getTBSCertListSignAlg c) (CRL.CertList.getCertListSignAlg c)

CRLr2 : ∀ {@0 bs} (c : CRL.CertList bs) → Dec (CRLR2 c)
CRLr2 c = CRL.CertList.getTBSCertListSignAlg c ≋? CRL.CertList.getCertListSignAlg c


-- The Issuer field MUST contain a non-empty distinguished name (DN).
CRLR3 : ∀ {@0 bs} → CRL.CertList bs → Set
CRLR3 c = 0 ≢ SequenceOf.length (Name.getRDNs (CRL.CertList.getIssuer c))

CRLr3 : ∀ {@0 bs} → (c : CRL.CertList bs) → Dec (CRLR3 c)
CRLr3 c = 0 ≠ _

--   when extensions are used, as required by this profile, version field MUST be
--   present and MUST specify version 2
CRLExtensionsPresent : ∀ {@0 bs} → CRL.CertList bs → Set
CRLExtensionsPresent c = T (isSome (CRL.CertList.getCRLExtensions c))

CRLR4 : ∀ {@0 bs} → CRL.CertList bs → Set
CRLR4 c = CRLExtensionsPresent c → getCRLDecodedVersion c ≡ v2

CRLr4 : ∀ {@0 bs} (c : CRL.CertList bs) → Dec (CRLR4 c)
CRLr4 c = T-dec →-dec _ ≟ v2

-- if CRLentry extensions, version = 2
CRLR5-helper : ∀ {@0 bs} → (c : CRL.CertList bs) → List (Exists─ (List UInt8) RevokedCertificate) → Set
CRLR5-helper c [] = ⊤
CRLR5-helper c ((fst , mkTLV len (mkRevokedCertificateFields cserial rdate none bs≡₁) len≡ bs≡) ∷ x₁) = CRLR5-helper c x₁
CRLR5-helper c ((fst , mkTLV len (mkRevokedCertificateFields cserial rdate (some ee) bs≡₁) len≡ bs≡) ∷ x₁) = getCRLDecodedVersion c ≡ v2

CRLR5 : ∀ {@0 bs} → CRL.CertList bs → Set
CRLR5 c = CRLR5-helper c (CRL.CertList.getRevokedCertificateList c)

CRLr5 : ∀ {@0 bs} → (c : CRL.CertList bs) → Dec (CRLR5 c)
CRLr5 c = helper (CRL.CertList.getRevokedCertificateList c)
  where
  helper : (rl : List (Exists─ (List UInt8) RevokedCertificate)) → Dec (CRLR5-helper c rl)
  helper [] = yes tt
  helper ((fst , mkTLV len (mkRevokedCertificateFields cserial rdate none bs≡₁) len≡ bs≡) ∷ x₁) = helper x₁
  helper ((fst , mkTLV len (mkRevokedCertificateFields cserial rdate (some ee) bs≡₁) len≡ bs≡) ∷ x₁) = getCRLDecodedVersion c ≟ v2


-- The certificate Validity period includes the current time
CRLR6 : ∀ {@0 bs₁ bs₂} → CRL.CertList bs₁ → Validity.Time bs₂ → Set
CRLR6 c t
  with CRL.CertList.getNextUpdate c
... | none = CertList.getThisUpdate c Time≤ t
... | some nu = (CertList.getThisUpdate c Time≤ t) × (t Time≤ nu)

CRLr6 : ∀ {@0 bs₁ bs₂} → (c : CRL.CertList bs₁) → (t : Validity.Time bs₂) → Dec (CRLR6 c t)
CRLr6 c t
  with CRL.CertList.getNextUpdate c
... | none = CertList.getThisUpdate c Time≤? t
... | some nu = (CertList.getThisUpdate c Time≤? t) ×-dec (t Time≤? nu)

-- freshest CRL extension MUST NOT appear in delta CRLs
CRLR7 : ∀ {@0 bs₁} → CRL.CertList bs₁ → Set
CRLR7 c = T (isDeltaCRL c) → T (isNone (proj₂ (CRL.CertList.getFCRL c)))

CRLr7 : ∀ {@0 bs₁} → (c : CRL.CertList bs₁) → Dec (CRLR7 c)
CRLr7 c = T-dec →-dec T-dec

-- If a key usage extension is present
-- in the CRL issuer's certificate, verify that the cRLSign bit
-- is set.
CRLR8-helper : List (Exists─ _ CRL.CertList) → List (Exists─ _ Cert) → Set
CRLR8-helper [] [] = ⊤
CRLR8-helper [] (x ∷ rest) = ⊥
CRLR8-helper (x ∷ rest) [] = ⊥
CRLR8-helper ((_ , crl) ∷ crls) ((_ , issuer) ∷ issuers) =
  NameMatch (CertList.getIssuer crl) (Cert.getSubject issuer) × IsConfirmedCRLIssuer issuer × CRLR8-helper crls issuers

CRLR8 : ∀ {@0 bs} {trustedRoot candidates : List (Exists─ _ Cert)} {cert : Cert bs}
       → Chain trustedRoot candidates cert →  List (Exists─ (List UInt8) CRL.CertList) → Set
CRLR8 chain crls
  with getIssuers chain
... | issuers = CRLR8-helper crls issuers

CRLr8 : ∀ {@0 bs} {trustedRoot candidates : List (Exists─ _ Cert)} {cert : Cert bs}
       → (chain : Chain trustedRoot candidates cert) →  (crls : List (Exists─ (List UInt8) CRL.CertList)) → Dec (CRLR8 chain crls)
CRLr8 chain crls
  with getIssuers chain
... | issuers = helper crls issuers
  where
  helper : (crls : List (Exists─ _ CRL.CertList)) → (issuers : List (Exists─ _ Cert)) → Dec (CRLR8-helper crls issuers)
  helper [] [] = yes tt
  helper [] (x ∷ rest) = no λ ()
  helper (x ∷ rest) [] = no λ ()
  helper ((_ , crl) ∷ crls) ((_ , issuer) ∷ issuers) =
    nameMatch? (CertList.getIssuer crl) (Cert.getSubject issuer) ×-dec isConfirmedCRLIssuer? issuer ×-dec helper crls issuers
