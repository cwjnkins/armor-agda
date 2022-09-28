{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Properties
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
open import Aeres.Grammar.IList as IList
open import Aeres.Prelude

module Aeres.Data.X509.Semantic.Cert where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8


------- helper functions -----

-- returns true iff time1 <= time2
checkTwoTimes : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Bool
checkTwoTimes yr₁ mn₁ da₁ hr₁ mi₁ se₁ yr₂ mn₂ da₂ hr₂ mi₂ se₂
  with yr₁ <? yr₂
...  | yes p₁ = true
...  | no ¬p₁
  with yr₂ <? yr₁
...  | yes p₂ = false
...  | no ¬p₂
  with mn₁ <? mn₂
...  | yes p₃ = true
...  | no ¬p₃
  with mn₂ <? mn₁
...  | yes p₄ = false
...  | no ¬p₄ 
  with da₁ <? da₂
...  | yes p₅ = true
...  | no ¬p₅ 
  with da₂ <? da₁
...  | yes p₆ = false
...  | no ¬p₆
  with hr₁ <? hr₂
...  | yes p₇ = true
...  | no ¬p₇
  with hr₂ <? hr₁
...  | yes p₈ = false
...  | no ¬p₈
  with mi₁ <? mi₂
...  | yes p₉ = true
...  | no ¬p₉
  with mi₂ <? mi₁
...  | yes p₁₀ = false
...  | no ¬p₁₀
  with se₁ <? se₂
...  | yes p₁₁ = true
...  | no ¬p₁₁
  with se₂ <? se₁
...  | yes p₁₂ = false
...  | no ¬p₁₂ = true


-- is it a CA certificate? the Basic Constraints extension is present and the value of CA is TRUE ?
isCA : Exists─ (List UInt8) (Option (X509.ExtensionFields (_≡ X509.ExtensionOID.BC) X509.BCFields)) → Bool
isCA (─ .[] , none) = false
isCA (fst , some (X509.mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (X509.mkBCFieldsSeqFields none bcpathlen bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isCA (fst , some (X509.mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (X509.mkBCFieldsSeqFields (some (mkTLV len₂ (mkBoolValue v b vᵣ bs≡₅) len≡₂ bs≡₄)) bcpathlen bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = v


-- returns BCPathLen if exists
getBCPathLen :  Exists─ (List UInt8) (Option (X509.ExtensionFields (_≡ X509.ExtensionOID.BC) X509.BCFields)) → Exists─ (List UInt8) (Option Int)
getBCPathLen (─ .[] , none) = _ , none
getBCPathLen (fst , some (X509.mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (X509.mkBCFieldsSeqFields bcca bcpathlen bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = _ , bcpathlen


-- isCRLSign present in KU extension ? bit 6 == true ?
isCRLIssuer : Exists─ (List UInt8) (Option (X509.ExtensionFields (_≡ X509.ExtensionOID.KU) X509.KUFields)) → Bool
isCRLIssuer (─ .[] , none) = false
isCRLIssuer (fst , some (X509.mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton [] x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isCRLIssuer (fst , some (X509.mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isCRLIssuer (fst , some (X509.mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isCRLIssuer (fst , some (X509.mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isCRLIssuer (fst , some (X509.mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isCRLIssuer (fst , some (X509.mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isCRLIssuer (fst , some (X509.mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isCRLIssuer (fst , some (X509.mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ x₆ ∷ x₇) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = x₆


-- isKeyCertSign present in KU extension ? bit 5 == true ?
isKeyCertSignPresent : Exists─ (List UInt8) (Option (X509.ExtensionFields (_≡ X509.ExtensionOID.KU) X509.KUFields)) → Bool
isKeyCertSignPresent (─ .[] , none) = false
isKeyCertSignPresent (fst , some (X509.mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton [] x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isKeyCertSignPresent (fst , some (X509.mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isKeyCertSignPresent (fst , some (X509.mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isKeyCertSignPresent (fst , some (X509.mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isKeyCertSignPresent (fst , some (X509.mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isKeyCertSignPresent (fst , some (X509.mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isKeyCertSignPresent (fst , some (X509.mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ x₆) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = x₅


-- get KU Bits in bool list
getKUBits : Exists─ (List UInt8) (Option (X509.ExtensionFields (_≡ X509.ExtensionOID.KU) X509.KUFields)) → List Bool
getKUBits (─ .[] , none) = []
getKUBits (fst , some (X509.mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton x x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = x


-- is SAN extension critical ? 
isSANCritical : Exists─ (List UInt8) (Option (X509.ExtensionFields (_≡ X509.ExtensionOID.SAN) X509.SANFields)) → Bool
isSANCritical (─ .[] , none) = false
isSANCritical (fst , some (X509.mkExtensionFields extnId extnId≡ none extension bs≡)) = false
isSANCritical (fst , some (X509.mkExtensionFields extnId extnId≡ (some (mkTLV len (mkBoolValue v b vᵣ bs≡₂) len≡ bs≡₁)) extension bs≡)) = v


-- get SAN length
getSANLength : Exists─ (List UInt8) (Option (X509.ExtensionFields (_≡ X509.ExtensionOID.SAN) X509.SANFields)) → ℕ
getSANLength (─ .[] , none) = 0
getSANLength (fst , some (X509.mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mk×ₚ fstₚ₁ sndₚ₁ bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = lengthSequence fstₚ₁


-- is SAN present in Cert ?
isSANPresent : Exists─ (List UInt8) (Option (X509.ExtensionFields (_≡ X509.ExtensionOID.SAN) X509.SANFields)) → Bool
isSANPresent (─ .[] , none) = false
isSANPresent (fst , some x) = true


-- helper for SCP17 :  While each of these fields is optional, a DistributionPoint MUST NOT consist of only the Reasons field;
-- either distributionPoint or CRLIssuer MUST be present.
checkCRLDistStruct : Exists─ (List UInt8) (Option (X509.ExtensionFields (_≡ X509.ExtensionOID.CRLDIST) X509.CRLDistFields)) → Bool
checkCRLDistStruct (─ .[] , none) = true
checkCRLDistStruct (fst , some (X509.mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mk×ₚ fstₚ₁ sndₚ₁ bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = helper fstₚ₁
  where
  helper : ∀ {@0 bs} → SequenceOf X509.DistPoint bs → Bool
  helper nil = true
  helper (cons (mkIListCons (mkTLV len (X509.mkDistPointFields crldp none crlissr bs≡₂) len≡ bs≡₁) t bs≡)) = true ∧ helper t
  helper (cons (mkIListCons (mkTLV len (X509.mkDistPointFields none (some x) none bs≡₂) len≡ bs≡₁) t bs≡)) = false
  helper (cons (mkIListCons (mkTLV len (X509.mkDistPointFields none (some x) (some x₁) bs≡₂) len≡ bs≡₁) t bs≡)) = true ∧ helper t
  helper (cons (mkIListCons (mkTLV len (X509.mkDistPointFields (some x₁) (some x) none bs≡₂) len≡ bs≡₁) t bs≡)) = true ∧ helper t
  helper (cons (mkIListCons (mkTLV len (X509.mkDistPointFields (some x₁) (some x) (some x₂) bs≡₂) len≡ bs≡₁) t bs≡)) = true ∧ helper t


-- returns all certificate policy OIDs
getPolicyOIDList : Exists─ (List UInt8) (Option (X509.ExtensionFields (_≡ X509.ExtensionOID.CPOL) X509.CertPolFields)) →  List (Exists─ (List UInt8) OID)
getPolicyOIDList (─ .[] , none) = []
getPolicyOIDList (fst , some (X509.mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ val len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = helper (fstₚ val)
  where
  helper : ∀ {@0 bs} → SequenceOf X509.PolicyInformation bs → List (Exists─ (List UInt8) OID)
  helper nil = []
  helper (cons (mkIListCons (mkTLV len (X509.mkPolicyInformationFields cpid cpqls bs≡₂) len≡ bs≡₁) t bs≡)) = (_ , cpid) ∷ (helper t)


-- returns true only if the extension is unknown and has critical bit = true
isUnkwnCriticalExtension : Exists─ (List UInt8) X509.Extension → Bool
isUnkwnCriticalExtension (fst , mkTLV len (X509.other (X509.mkExtensionFields extnId extnId≡ none extension bs≡₁)) len≡ bs≡) = false
isUnkwnCriticalExtension (fst , mkTLV len (X509.other (X509.mkExtensionFields extnId extnId≡ (some (mkTLV len₁ (mkBoolValue v b vᵣ bs≡₃) len≡₁ bs≡₂)) extension bs≡₁)) len≡ bs≡) = v
isUnkwnCriticalExtension (fst , mkTLV len _ len≡ bs≡) = false

-- is any unknown extention critical from the list ?
isAnyOtherExtnCritical : List (Exists─ (List UInt8) X509.Extension) → Bool
isAnyOtherExtnCritical x = helper x
  where
  -- returns true only if at least one extension in the list is unknown and that extension has critical bit = true
  helper : List (Exists─ (List UInt8) X509.Extension) → Bool
  helper [] = false
  helper (x ∷ x₁) = case (isUnkwnCriticalExtension x) of λ where
    false → helper x₁
    true → true


getExtensionsOIDList : List (Exists─ (List UInt8) X509.Extension) →  List (Exists─ (List UInt8) OID)
getExtensionsOIDList = map helper
  where
  helper : Exists─ (List UInt8) X509.Extension → (Exists─ (List UInt8) OID)
  helper (fst , mkTLV len (X509.akiextn x) len≡ bs≡) = _ , (X509.ExtensionFields.extnId x)
  helper (fst , mkTLV len (X509.skiextn x) len≡ bs≡) = _ , (X509.ExtensionFields.extnId x)
  helper (fst , mkTLV len (X509.kuextn x) len≡ bs≡) = _ , (X509.ExtensionFields.extnId x)
  helper (fst , mkTLV len (X509.ekuextn x) len≡ bs≡) = _ , (X509.ExtensionFields.extnId x)
  helper (fst , mkTLV len (X509.bcextn x) len≡ bs≡) = _ , (X509.ExtensionFields.extnId x)
  helper (fst , mkTLV len (X509.ianextn x) len≡ bs≡) = _ , (X509.ExtensionFields.extnId x)
  helper (fst , mkTLV len (X509.sanextn x) len≡ bs≡) = _ , (X509.ExtensionFields.extnId x)
  helper (fst , mkTLV len (X509.cpextn x) len≡ bs≡) = _ , (X509.ExtensionFields.extnId x)
  helper (fst , mkTLV len (X509.crlextn x) len≡ bs≡) = _ , (X509.ExtensionFields.extnId x)
  helper (fst , mkTLV len (X509.ncextn x) len≡ bs≡) = _ , (X509.ExtensionFields.extnId x)
  helper (fst , mkTLV len (X509.pcextn x) len≡ bs≡) = _ , (X509.ExtensionFields.extnId x)
  helper (fst , mkTLV len (X509.pmextn x) len≡ bs≡) = _ , (X509.ExtensionFields.extnId x)
  helper (fst , mkTLV len (X509.inapextn x) len≡ bs≡) = _ , (X509.ExtensionFields.extnId x)
  helper (fst , mkTLV len (X509.aiaextn x) len≡ bs≡) = _ , (X509.ExtensionFields.extnId x)
  helper (fst , mkTLV len (X509.other x) len≡ bs≡) = _ , (X509.ExtensionFields.extnId x)


-- SignatureAlgorithm field MUST contain the same algorithm identifier as
-- the Signature field in the sequence TbsCertificate.
SCP1 : ∀ {@0 bs} → X509.Cert bs → Set
SCP1 c = X509.Cert.getTBSCertSignAlg c ≡ X509.Cert.getCertSignAlg c

scp1 :  ∀ {@0 bs} (c : X509.Cert bs) → Dec (SCP1 c)
scp1 c
  with proj₂ (X509.Cert.getTBSCertSignAlg c) ≋? proj₂ (X509.Cert.getCertSignAlg c)
... | no ¬p = no (λ { refl → contradiction (mk≋ refl refl) ¬p})
... | yes (mk≋ refl refl) = yes refl


-- Extension field MUST only appear if the Version is 3(2).
SCP2 : ∀ {@0 bs} → X509.Cert bs → Set
SCP2 c = T (isSome (proj₂ (X509.Cert.getExtensions c))) → X509.Cert.getVersion c ≡ ℤ.+ 2

scp2 : ∀ {@0 bs} (c : X509.Cert bs) → Dec (SCP2 c)
scp2 c =
  case proj₂ (X509.Cert.getExtensions c) ret (λ x → Dec (T (isSome x) → X509.Cert.getVersion c ≡ ℤ.+ 2)) of λ where
    none → yes (λ ())
    (some x) →
      case X509.Cert.getVersion c ≟ ℤ.+ 2 of λ where
        (no ¬p) → no (λ abs → contradiction (abs tt) ¬p)
        (yes p) → yes (λ _ → p)

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
scp7₁ c =
  case proj₂ (X509.Cert.getSubUID c) ret (λ x → Dec (T (isSome x) → X509.Cert.getVersion c ≡ ℤ.+ 1 ⊎ X509.Cert.getVersion c ≡  ℤ.+ 2)) of λ where
    none → yes λ ()
    (some x) →
      case (X509.Cert.getVersion c ≟ ℤ.+ 1 ⊎-dec X509.Cert.getVersion c ≟ ℤ.+ 2) of λ where
        (no ¬p) → no (λ abs → contradiction (abs tt) ¬p)
        (yes p) → yes (λ _ → p)

scp7₂ : ∀ {@0 bs} (c : X509.Cert bs) → Dec (SCP7₂ c)
scp7₂ c =
  case proj₂ (X509.Cert.getIssUID c) ret (λ x → Dec (T (isSome x) → X509.Cert.getVersion c ≡ ℤ.+ 1 ⊎ X509.Cert.getVersion c ≡  ℤ.+ 2)) of (λ where
    none → yes (λ ())
    (some _) →
      case (X509.Cert.getVersion c ≟ ℤ.+ 1 ⊎-dec X509.Cert.getVersion c ≟ ℤ.+ 2) of λ where
        (no ¬p) → no (λ abs → contradiction (abs tt) ¬p)
        (yes p) → yes λ _ → p)

-- Where it appears, the PathLenConstraint field MUST be greater than or equal to zero.
SCP8' : Exists─ (List UInt8) (Option Int) → Set
SCP8' (─ .[] , none) = ⊤
SCP8' (fst , some x) = ℤ.+ 0 ℤ.≤ Int.getVal x

SCP8 : ∀ {@0 bs} → X509.Cert bs → Set
SCP8 c = SCP8' (getBCPathLen (X509.Cert.getBC c))

scp8 : ∀ {@0 bs} (c : X509.Cert bs) → Dec (SCP8 c)
scp8 c =
  case (getBCPathLen (X509.Cert.getBC c)) ret (λ x → Dec (SCP8' x)) of λ where
    (─ .[] , none) → yes tt
    (fst , some x) → ℤ.+ 0 ℤ.≤? Int.getVal x

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
SCP17 : ∀ {@0 bs} → X509.Cert bs → Set
SCP17 c = T (checkCRLDistStruct (X509.Cert.getCRLDIST c))

scp17 : ∀ {@0 bs} (c : X509.Cert bs) → Dec (SCP17 c)
scp17 c
  with checkCRLDistStruct (X509.Cert.getCRLDIST c)
... | false = no (λ x → x)
... | true = yes tt


-- The certificate Validity period includes the current time
SCP18 : ∀ {@0 bs₁ bs₂} → X509.Cert bs₁ → Time bs₂ → Set
SCP18 c t = T (Time.lessEq (proj₂ (X509.Cert.getValidityStartTime c)) t ∧ Time.lessEq t (proj₂ (X509.Cert.getValidityEndTime c)))

scp18 : ∀ {@0 bs₁ bs₂} → (c : X509.Cert bs₁) → (t : Time bs₂) → Dec (SCP18 c t)
scp18 c t
  with Time.lessEq (proj₂ (X509.Cert.getValidityStartTime c)) t ∧ Time.lessEq t (proj₂ (X509.Cert.getValidityEndTime c))
... | false = no id
... | true  = yes tt

