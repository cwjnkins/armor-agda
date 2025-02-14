open import Armor.Binary
open import Armor.Data.X509
open import Armor.Data.X509.CRL.CertList.TCB as CRL
open import Armor.Data.X509.CRL.Version
open import Armor.Data.X509.CRL.RevokedCertificates
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
import Armor.Grammar.Parallel.TCB
open import Armor.Grammar.IList as IList
open import Armor.Prelude
open import Relation.Nullary.Implication

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
R1 : ∀ {@0 bs} → CRL.CertList bs → Set
R1 c = getCRLDecodedVersion c ≡ v2

r1 : ∀ {@0 bs} → (c : CRL.CertList bs) → Dec (R1 c)
r1 c = getCRLDecodedVersion c ≟ v2


-- Signature Algorithm field MUST contain the same algorithm identifier as the
--   signature field in the sequence tbsCertList
R2 : ∀ {@0 bs} → CRL.CertList bs → Set
R2 c = _≋_{A = SignAlg} (CRL.CertList.getTBSCertListSignAlg c) (CRL.CertList.getCertListSignAlg c)

r2 : ∀ {@0 bs} (c : CRL.CertList bs) → Dec (R2 c)
r2 c = CRL.CertList.getTBSCertListSignAlg c ≋? CRL.CertList.getCertListSignAlg c


-- The Issuer field MUST contain a non-empty distinguished name (DN).
R3 : ∀ {@0 bs} → CRL.CertList bs → Set
R3 c = 0 ≢ SequenceOf.length (Name.getRDNs (CRL.CertList.getIssuer c))

r3 : ∀ {@0 bs} → (c : CRL.CertList bs) → Dec (R3 c)
r3 c = 0 ≠ _

--   when extensions are used, as required by this profile, version field MUST be
--   present and MUST specify version 2
CRLExtensionsPresent : ∀ {@0 bs} → CRL.CertList bs → Set
CRLExtensionsPresent c = T (isSome (CRL.CertList.getCRLExtensions c))

R4 : ∀ {@0 bs} → CRL.CertList bs → Set
R4 c = CRLExtensionsPresent c → getCRLDecodedVersion c ≡ v2

r4 : ∀ {@0 bs} (c : CRL.CertList bs) → Dec (R4 c)
r4 c = T-dec →-dec _ ≟ v2

-- if CRLentry extensions, version = 2
R5-helper : ∀ {@0 bs} → (c : CRL.CertList bs) → List (Exists─ (List UInt8) RevokedCertificate) → Set
R5-helper c [] = ⊤
R5-helper c ((fst , mkTLV len (mkRevokedCertificateFields cserial rdate none bs≡₁) len≡ bs≡) ∷ x₁) = R5-helper c x₁
R5-helper c ((fst , mkTLV len (mkRevokedCertificateFields cserial rdate (some ee) bs≡₁) len≡ bs≡) ∷ x₁) = getCRLDecodedVersion c ≡ v2

R5 : ∀ {@0 bs} → CRL.CertList bs → Set
R5 c = R5-helper c (CRL.CertList.getRevokedCertificateList c)

r5 : ∀ {@0 bs} → (c : CRL.CertList bs) → Dec (R5 c)
r5 c = helper (CRL.CertList.getRevokedCertificateList c)
  where
  helper : (rl : List (Exists─ (List UInt8) RevokedCertificate)) → Dec (R5-helper c rl)
  helper [] = yes tt
  helper ((fst , mkTLV len (mkRevokedCertificateFields cserial rdate none bs≡₁) len≡ bs≡) ∷ x₁) = helper x₁
  helper ((fst , mkTLV len (mkRevokedCertificateFields cserial rdate (some ee) bs≡₁) len≡ bs≡) ∷ x₁) = getCRLDecodedVersion c ≟ v2
