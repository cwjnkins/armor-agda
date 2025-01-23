{-# OPTIONS --sized-types #-}

open import Armor.Binary
open import Armor.Data.X509
open import Armor.Data.X509.CRL.CertList.TCB as CRL
open import Armor.Data.X509.CRL.Extension.TCB as CRLExtension
open import Armor.Data.X509.Semantic.Chain.NameMatch
open import Armor.Data.X509.CRL.Extension.IDP.TCB as IDP
open import Armor.Data.X509.Extension.CRLDistPoint.DistPoint.Name.TCB
open import Armor.Data.X509.CRL.RevokedCertificates.TCB
open import Armor.Data.X509.CRL.RevokedCertificates.EntryExtension.TCB
-- import      Armor.Data.X509.Extension.TCB.OIDs as OIDs
open import Armor.Data.X509.CRL.Semantic.Utils
open import Armor.Data.X509.Extension.CRLDistPoint.DistPoint.TCB as DP
open import Armor.Data.X509.GeneralNames.GeneralName.TCB
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
open import Armor.Grammar.IList as IList
import      Armor.Grammar.Parallel.TCB
open import Armor.Prelude

module Armor.Data.X509.CRL.Semantic.Validation where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8
open Armor.Grammar.Parallel.TCB UInt8

-- -- -- R1 : ∀ {@0 bs} → Cert bs → Set
-- -- -- R1 c = _≋_{A = SignAlg} (Cert.getTBSCertSignAlg c) (Cert.getCertSignAlg c)

-- -- -- r1 : ∀ {@0 bs} (c : Cert bs) → Dec (R1 c)
-- -- -- r1 c = Cert.getTBSCertSignAlg c ≋? Cert.getCertSignAlg c

-- Helper function to check equality of RevocationReason
revocationReasonEq : RevocationReason → RevocationReason → Bool
revocationReasonEq allReasons allReasons = true
revocationReasonEq keyCompromise keyCompromise = true
revocationReasonEq cACompromise cACompromise = true
revocationReasonEq affiliationChanged affiliationChanged = true
revocationReasonEq superseded superseded = true
revocationReasonEq cessationOfOperation cessationOfOperation = true
revocationReasonEq certificateHold certificateHold = true
revocationReasonEq privilegeWithdrawn privilegeWithdrawn = true
revocationReasonEq aACompromise aACompromise = true
revocationReasonEq _ _ = false

certStatusEq : CertStatus → CertStatus → Bool
certStatusEq unspecified unspecified = true
certStatusEq keyCompromise keyCompromise = true
certStatusEq cACompromise cACompromise = true
certStatusEq affiliationChanged affiliationChanged = true
certStatusEq superseded superseded = true
certStatusEq cessationOfOperation cessationOfOperation = true
certStatusEq certificateHold certificateHold = true
certStatusEq removeFromCRL removeFromCRL = true
certStatusEq privilegeWithdrawn privilegeWithdrawn = true
certStatusEq aACompromise aACompromise = true
certStatusEq UNREVOKED UNREVOKED = true
certStatusEq UNDETERMINED UNDETERMINED = true
certStatusEq _ _ = false


findInList : RevocationReason → List RevocationReason → Bool
findInList x [] = false
findInList x (x₁ ∷ x₂) =
  if revocationReasonEq x x₁
    then true
  else findInList x x₂

findInList' : List RevocationReason → List RevocationReason → Bool
findInList' [] x₁ = false
findInList' (x ∷ x₂) x₁ =
  if findInList x x₁
    then true
  else findInList' x₂ x₁

notFindInList' : List RevocationReason → List RevocationReason → Bool
notFindInList' [] x₁ = false
notFindInList' (x ∷ x₂) x₁ =
  if not (findInList x x₁)
    then true
  else notFindInList' x₂ x₁

atLeastOneCmnGN : ∀{@0 bs₁ bs₂} → SequenceOf GeneralName bs₁ → SequenceOf GeneralName bs₂ → Bool
atLeastOneCmnGN nil nil = false
atLeastOneCmnGN nil (cons x) = false
atLeastOneCmnGN (cons x) nil = false
atLeastOneCmnGN (cons (mkIListCons head₁ tail₁ bs≡)) (cons x₁) =
  case helper head₁ (cons x₁) of λ where
    true → true
    false → atLeastOneCmnGN tail₁ (cons x₁)
  where
  helper : ∀{@0 bs₁ bs₂} → GeneralName bs₁ → SequenceOf GeneralName bs₂ → Bool
  helper x nil = false
  helper x (cons (mkIListCons head₂ tail₂ bs≡)) =
    case (_≋?_ {A = GeneralName} x head₂) of λ where
      (no _) → helper x tail₂
      (yes _) → true

-- Find common RevocationReason between two lists
commRevocationReason : List RevocationReason → List RevocationReason → List RevocationReason
commRevocationReason [] [] = []
commRevocationReason [] ys = []
commRevocationReason xs [] = []
commRevocationReason (x ∷ xs) (y ∷ ys) =
  if revocationReasonEq x y
    then x ∷ commRevocationReason xs ys
  else commRevocationReason xs (y ∷ ys)

-- Find union RevocationReason between two lists
unonRevocationReason : List RevocationReason → List RevocationReason → List RevocationReason
unonRevocationReason [] [] = []
unonRevocationReason [] ys = ys
unonRevocationReason xs [] = xs
unonRevocationReason (x ∷ xs) (y ∷ ys) =
  if revocationReasonEq x y
    then x ∷ unonRevocationReason xs ys
  else x ∷ y ∷ unonRevocationReason xs ys

dpReasonsBitsToList : ∀{@0 bs} → DP.ReasonFlags bs → List RevocationReason
dpReasonsBitsToList (mkTLV len (mkBitStringValue bₕ bₜ bₕ<8 (singleton x x≡) unusedBits bs≡₁) len≡ bs≡) = boolListToReasons x

idpReasonsBitsToList : ∀{@0 bs} → IDP.ReasonFlags bs → List RevocationReason
idpReasonsBitsToList (mkTLV len (mkBitStringValue bₕ bₜ bₕ<8 (singleton x x≡) unusedBits bs≡₁) len≡ bs≡) = boolListToReasons x

dpHasCrlissr : ∀{@0 bs} → DistPoint bs → Bool
dpHasCrlissr (mkTLV len (mkDistPointFields dpname rsn none notOnlyReasonT bs≡₁) len≡ bs≡) = false
dpHasCrlissr (mkTLV len (mkDistPointFields dpname rsn (some _) notOnlyReasonT bs≡₁) len≡ bs≡) = true

dpHasDPname : ∀{@0 bs} → DistPoint bs → Bool
dpHasDPname (mkTLV len (mkDistPointFields none rsn issr notOnlyReasonT bs≡₁) len≡ bs≡) = false
dpHasDPname (mkTLV len (mkDistPointFields (some _) rsn issr notOnlyReasonT bs≡₁) len≡ bs≡) = true

dpHasRsn : ∀{@0 bs} → DistPoint bs → Bool
dpHasRsn (mkTLV len (mkDistPointFields dpname none issr notOnlyReasonT bs≡₁) len≡ bs≡) = false
dpHasRsn (mkTLV len (mkDistPointFields dpname (some _) issr notOnlyReasonT bs≡₁) len≡ bs≡) = true

idpPresent : ∀{@0 bs} → CRL.CertList bs → Bool
idpPresent crl = case CRL.CertList.getIDP crl of λ where
      (_ , none) → false
      (_ , some _) → true

idpHasDPname : ∀{@0 bs} → CRL.CertList bs → Bool
idpHasDPname crl = case CRL.CertList.getIDP crl of λ where
      (_ , none) → false
      (_ , some (mkExtensionFields _ _ _ (mkTLV _ (mkTLV _ (mkIDPFieldsSeqFields none _ _ _ _ _ _ _) _ _) _ _) _)) → false
      (_ , some (mkExtensionFields _ _ _ (mkTLV _ (mkTLV _ (mkIDPFieldsSeqFields (some _) _ _ _ _ _ _ _) _ _) _ _) _)) → true

idpHasOnlySmRsn : ∀{@0 bs} → CRL.CertList bs → Bool
idpHasOnlySmRsn crl = case CRL.CertList.getIDP crl of λ where
      (_ , none) → false
      (_ , some (mkExtensionFields _ _ _ (mkTLV _ (mkTLV _ (mkIDPFieldsSeqFields _ _ _ none _ _ _ _) _ _) _ _) _)) → false
      (_ , some (mkExtensionFields _ _ _ (mkTLV _ (mkTLV _ (mkIDPFieldsSeqFields _ _ _ (some _) _ _ _ _) _ _) _ _) _)) → true

indirectCRLtrue : ∀ {@0 bs} → CRL.CertList bs → Bool
indirectCRLtrue crl = case CRL.CertList.getIDP crl of λ where
      (_ , none) → false
      (_ , some (mkExtensionFields _ _ _ (mkTLV _ (mkTLV _ (mkIDPFieldsSeqFields _ _ _ _ (mkDefault none notDefault) _ _ _) _ _) _ _) _)) → false
      (_ , some (mkExtensionFields _ _ _ (mkTLV _ (mkTLV _ (mkIDPFieldsSeqFields _ _ _ _
        (mkDefault (some (mkTLV _ (mkBoolValue v _ _ _) _ _)) notDefault) _ _ _) _ _) _ _) _)) → v

onlyUserCertstrue : ∀ {@0 bs} → CRL.CertList bs → Bool
onlyUserCertstrue crl = case CRL.CertList.getIDP crl of λ where
      (_ , none) → false
      (_ , some (mkExtensionFields _ _ _ (mkTLV _ (mkTLV _ (mkIDPFieldsSeqFields _  (mkDefault none notDefault) _ _ _ _ _ _) _ _) _ _) _)) → false
      (_ , some (mkExtensionFields _ _ _ (mkTLV _ (mkTLV _ (mkIDPFieldsSeqFields _ 
        (mkDefault (some (mkTLV _ (mkBoolValue false _ _ _) _ _)) notDefault) _ _ _ _ _ _) _ _) _ _) _)) → false
      (_ , some (mkExtensionFields _ _ _ (mkTLV _ (mkTLV _ (mkIDPFieldsSeqFields _
        (mkDefault (some (mkTLV _ (mkBoolValue true _ _ _) _ _)) notDefault) _ _ _ _ _ _) _ _) _ _) _)) → true

onlyCACertstrue : ∀ {@0 bs} → CRL.CertList bs → Bool
onlyCACertstrue crl = case CRL.CertList.getIDP crl of λ where
      (_ , none) → false
      (_ , some (mkExtensionFields _ _ _ (mkTLV _ (mkTLV _ (mkIDPFieldsSeqFields _ _ (mkDefault none notDefault) _ _ _ _ _) _ _) _ _) _)) → false
      (_ , some (mkExtensionFields _ _ _ (mkTLV _ (mkTLV _ (mkIDPFieldsSeqFields _ _
        (mkDefault (some (mkTLV _ (mkBoolValue false _ _ _) _ _)) notDefault) _ _ _ _ _) _ _) _ _) _)) → false
      (_ , some (mkExtensionFields _ _ _ (mkTLV _ (mkTLV _ (mkIDPFieldsSeqFields _ _
        (mkDefault (some (mkTLV _ (mkBoolValue true _ _ _) _ _)) notDefault) _ _ _ _ _) _ _) _ _) _)) → true

onlyAttCertsfalse : ∀ {@0 bs} → CRL.CertList bs → Bool
onlyAttCertsfalse crl = case CRL.CertList.getIDP crl of λ where
      (_ , none) → true
      (_ , some (mkExtensionFields _ _ _ (mkTLV _ (mkTLV _ (mkIDPFieldsSeqFields _ _ _ _ _ (mkDefault none notDefault) _ _) _ _) _ _) _)) → true
      (_ , some (mkExtensionFields _ _ _ (mkTLV _ (mkTLV _ (mkIDPFieldsSeqFields _ _ _ _ _
        (mkDefault (some (mkTLV _ (mkBoolValue false _ _ _) _ _)) notDefault) _ _) _ _) _ _) _)) → true
      (_ , some (mkExtensionFields _ _ _ (mkTLV _ (mkTLV _ (mkIDPFieldsSeqFields _ _ _ _ _
        (mkDefault (some (mkTLV _ (mkBoolValue true _ _ _) _ _)) notDefault) _ _) _ _) _ _) _)) → false

crlIssuerMatchesDPcrlissuer : ∀{@0 bs₁ bs₂} → DistPoint bs₁ → CRL.CertList bs₂ → Bool
crlIssuerMatchesDPcrlissuer (mkTLV len (mkDistPointFields dpname rsn none notOnlyReasonT bs≡₁) len≡ bs≡) crl = false
crlIssuerMatchesDPcrlissuer (mkTLV len (mkDistPointFields dpname rsn
  (some (mkTLV len₁ (mk×ₚ fstₚ₁ sndₚ₁) len≡₁ bs≡₂)) notOnlyReasonT bs≡₁) len≡ bs≡) crl = helper₁ fstₚ₁
  where
    helper₁ : ∀ {@0 bs} → SequenceOf GeneralName bs → Bool
    helper₁ nil = false
    helper₁ (cons (mkIListCons (dirname (mkTLV len issr len≡ bs≡₁)) tail₁ bs≡)) =
      case nameMatch? issr (CRL.CertList.getIssuer crl) of λ where
        (no _) → helper₁ tail₁
        (yes _) → true
    helper₁ (cons (mkIListCons _ tail₁ bs≡)) = helper₁ tail₁
 
crlIssuerMatchesCertIssuer : ∀ {@0 bs₁ bs₂} → Cert bs₁ → CRL.CertList bs₂ → Bool
crlIssuerMatchesCertIssuer cert crl =
  case nameMatch? (Cert.getIssuer cert) (CRL.CertList.getIssuer crl) of λ where
    (no _) → false
    (yes _) → true

idpDpnameMatchesDPdpname : ∀{@0 bs₁ bs₂} → DistPoint bs₁ → CRL.CertList bs₂ → Bool
idpDpnameMatchesDPdpname (mkTLV len (mkDistPointFields none crldprsn crlissr notOnlyReasonT bs≡₁) len≡ bs≡) crl = false
idpDpnameMatchesDPdpname (mkTLV len (mkDistPointFields (some (mkTLV len₁ valdp len≡₁ bs≡₂)) crldprsn crlissr notOnlyReasonT bs≡₁) len≡ bs≡) crl =
  case CRL.CertList.getIDP crl of λ where
      (_ , none) → false
      (_ , some (mkExtensionFields _ _ _ (mkTLV _ (mkTLV _ (mkIDPFieldsSeqFields none _ _ _ _ _ _ _) _ _) _ _) _)) → false
      (_ , some (mkExtensionFields _ _ _ (mkTLV _ (mkTLV _ (mkIDPFieldsSeqFields (some (mkTLV len validp len≡ bs≡)) _ _ _ _ _ _ _) _ _) _ _) _)) →
          helper valdp validp
        where
        helper : ∀{@0 bs₁ bs₂} → DistPointNameChoice bs₁ → DistPointNameChoice bs₂ → Bool
        helper (fullname (mkTLV len (mk×ₚ fstₚ₁ sndₚ₁) len≡ bs≡)) (fullname (mkTLV len₁ (mk×ₚ fstₚ₂ sndₚ₂) len≡₁ bs≡₁)) =
          atLeastOneCmnGN fstₚ₁ fstₚ₂
        helper (fullname _) (nameRTCrlissr _) = false
        helper (nameRTCrlissr _) (fullname _) = false
        helper (nameRTCrlissr (mkTLV len val len≡ bs≡)) (nameRTCrlissr (mkTLV len₁ val₁ len≡₁ bs≡₁)) =
          case []rdnMatch? val val₁ of λ where
            (no _) → false
            (yes _) → true

idpDpnameMatchesDPcrlissuer : ∀{@0 bs₁ bs₂} → DistPoint bs₁ → CRL.CertList bs₂ → Bool
idpDpnameMatchesDPcrlissuer (mkTLV len (mkDistPointFields crldp crldprsn none notOnlyReasonT bs≡₁) len≡ bs≡) crl = false
idpDpnameMatchesDPcrlissuer (mkTLV len (mkDistPointFields crldp crldprsn (some valissr) notOnlyReasonT bs≡₁) len≡ bs≡) crl =
  case CRL.CertList.getIDP crl of λ where
      (_ , none) → false
      (_ , some (mkExtensionFields _ _ _ (mkTLV _ (mkTLV _ (mkIDPFieldsSeqFields none _ _ _ _ _ _ _) _ _) _ _) _)) → false
      (_ , some (mkExtensionFields _ _ _ (mkTLV _ (mkTLV _ (mkIDPFieldsSeqFields (some (mkTLV len validp len≡ bs≡)) _ _ _ _ _ _ _) _ _) _ _) _)) →
        helper validp valissr
        where
        helper : ∀{@0 bs₁ bs₂} → DistPointNameChoice bs₁ → CrlIssuer bs₂ → Bool
        helper (fullname (mkTLV len₁ (mk×ₚ fstₚ₁ sndₚ₁) len≡₁ bs≡₁)) (mkTLV len (mk×ₚ fstₚ₂ sndₚ₂) len≡ bs≡) = atLeastOneCmnGN fstₚ₁ fstₚ₂
        helper (nameRTCrlissr x) (mkTLV len val len≡ bs≡) = false

certIsCA : ∀ {@0 bs} → Cert bs → Bool
certIsCA cert = case Cert.isCA cert of λ where
  (just false) → false
  (just true) → true
  nothing → false

certIsNotCA : ∀ {@0 bs} → Cert bs → Bool
certIsNotCA cert = case Cert.isCA cert of λ where
  (just false) → true
  (just true) → false
  nothing → true


BscopeCompleteCRL : ∀{@0 bs₁ bs₂ bs₃} → Cert bs₁ → DistPoint bs₂ → CRL.CertList bs₃ → Bool
BscopeCompleteCRL cert dp crl =
  let
          b1 : ∀{@0 bs} → DistPoint bs → Bool
          b1 dp =
            if (dpHasCrlissr dp) then
              (crlIssuerMatchesDPcrlissuer dp crl) ∧ (indirectCRLtrue crl)
            else
              (crlIssuerMatchesCertIssuer cert crl)

          b21 :  ∀{@0 bs} → DistPoint bs → Bool
          b21 dp =
              if idpPresent crl then
                 if (idpHasDPname crl)  then
                   if dpHasDPname dp then
                     idpDpnameMatchesDPdpname dp crl
                   else
                     idpDpnameMatchesDPcrlissuer dp crl
                 else true
              else true

          b22 :  Bool
          b22 =
              if idpPresent crl ∧ onlyUserCertstrue crl then
                certIsNotCA cert
              else true

          b23 : Bool
          b23 =
              if idpPresent crl ∧ onlyCACertstrue crl then
                certIsCA cert
              else true

          b24 : Bool
          b24 =
              if idpPresent crl then
                onlyAttCertsfalse crl
              else true

          b2 :  ∀{@0 bs} → DistPoint bs → Bool
          b2 dp = b21 dp ∧ b22 ∧ b23 ∧ b24
  in
  (b1 dp ∧ b2 dp)

CscopeDeltaCRL : ∀{@0 bs₁ bs₂} → Bool → CRL.CertList bs₁ → Maybe (CRL.CertList bs₂) → Bool
CscopeDeltaCRL false crl _ = true
CscopeDeltaCRL true crl nothing = false
CscopeDeltaCRL true crl (just delta) =
  case nameMatch? (CRL.CertList.getIssuer crl) (CRL.CertList.getIssuer delta) of λ where
    (no _) → false
    (yes _) →
      case CRL.CertList.getIDP crl of λ where
        (_ , none) →
          case CRL.CertList.getIDP delta of λ where
            (_ , none) → akiMatch
            (_ , some y) → false
        (_ , some x) →
          case CRL.CertList.getIDP delta of λ where
            (_ , none) → false
            (_ , some y) → akiMatch
  where
  akiMatch : Bool
  akiMatch =
    case CRL.CertList.getAKI crl of λ where
      (_ , none) →
        case CRL.CertList.getAKI delta of λ where
          (_ , none) → true
          (_ , some (mkExtensionFields _ _ _ (mkTLV _ (mkTLV _ val₁ _ _) _ _) _)) → false
      (_ , some (mkExtensionFields _ _ _ (mkTLV _ (mkTLV _ val₁ _ _) _ _) _)) →
        case CRL.CertList.getAKI delta of λ where
          (_ , none) → false
          (_ , some (mkExtensionFields _ _ _ (mkTLV _ (mkTLV _ val₂ _ _) _ _) _)) →
            case _≋?_ val₁ val₂ of λ where
              (no _) → false
              (yes _) → true

DcomputeIntReasonMask :  ∀{@0 bs₁ bs₂} → DistPoint bs₁ → CRL.CertList bs₂ → List RevocationReason
DcomputeIntReasonMask (mkTLV len (mkDistPointFields crldp none crlissr notOnlyReasonT bs≡₁) len≡ bs≡) crl =
  case CRL.CertList.getIDP crl of λ where
      (_ , none) → [ allReasons ]
      (_ , some (mkExtensionFields _ _ _ (mkTLV _ (mkTLV _ (mkIDPFieldsSeqFields _ _ _ none _ _ _ _) _ _) _ _) _)) → [ allReasons ]
      (_ , some (mkExtensionFields _ _ _ (mkTLV _ (mkTLV _ (mkIDPFieldsSeqFields _ _ _ (some x) _ _ _ _) _ _) _ _) _)) → idpReasonsBitsToList x
DcomputeIntReasonMask (mkTLV len (mkDistPointFields crldp (some x) crlissr notOnlyReasonT bs≡₁) len≡ bs≡) crl =
  case CRL.CertList.getIDP crl of λ where
      (_ , none) → dpReasonsBitsToList x
      (_ , some (mkExtensionFields _ _ _ (mkTLV _ (mkTLV _ (mkIDPFieldsSeqFields _ _ _ none _ _ _ _) _ _) _ _) _)) → dpReasonsBitsToList x
      (_ , some (mkExtensionFields _ _ _ (mkTLV _ (mkTLV _ (mkIDPFieldsSeqFields _ _ _ (some y) _ _ _ _) _ _) _ _) _)) →
        commRevocationReason (dpReasonsBitsToList x) (idpReasonsBitsToList y)

-- Verify that interim_reasons_mask includes one or more reasons
--            that are not included in the reasons_mask.
EverifiyMask : List RevocationReason → List RevocationReason → Bool
EverifiyMask reasonsMask interimReasonsMask = notFindInList' interimReasonsMask reasonsMask

-- If (cert_status is UNREVOKED), then search for the
           -- certificate on the complete CRL.  If an entry is found that
           -- matches the certificate issuer and serial number as described
           -- in Section 5.3.3, then set the cert_status variable to the
           -- indicated reason as described in step (i).

JfindSerialIssuerMatch : ∀{@0 bs₁ bs₂} → Cert bs₁ → CRL.CertList bs₂ → Maybe (Exists─ (List UInt8) RevokedCertificate)
JfindSerialIssuerMatch cert crl =
  case CRL.CertList.getRevokedCertificateList crl of λ where
    v → if indirectCRLtrue crl then (helper₂{[]} v nothing) else helper₁ v
      where
      matchCertIssExtnWithCertIssuer : ∀{@0 bs} → ExtensionFieldCertIssuer bs → Bool
      matchCertIssExtnWithCertIssuer (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mk×ₚ fstₚ₁ sndₚ₁) len≡₁ bs≡₂) len≡ bs≡₁) bs≡) = helper fstₚ₁
        where
        helper : ∀{@0 bs} → SequenceOf GeneralName bs → Bool
        helper nil = false
        helper (cons (mkIListCons (dirname (mkTLV len val len≡ bs≡₁)) tail₁ bs≡)) =
          case (_≋?_{A = Name} (Cert.getIssuer cert) val) of λ where
            (no _) → helper tail₁
            (yes _) → true
        helper (cons (mkIListCons _ tail₁ bs≡)) = helper tail₁

      matchCertIssExtnWithIAN : ∀{@0 bs} → ExtensionFieldCertIssuer bs → Bool
      matchCertIssExtnWithIAN (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mk×ₚ val₁ sndₚ₁) len≡₁ bs≡₂) len≡ bs≡₁) bs≡) =
        case Cert.getIAN cert of λ where
          (─ .[] , none) → false
          (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mk×ₚ val₂ sndₚ₁) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) → atLeastOneCmnGN val₁ val₂

      matchCRLIssuerWithCertIssuer : Bool
      matchCRLIssuerWithCertIssuer =
        case _≋?_{A = Name} (CRL.CertList.getIssuer crl) (Cert.getIssuer cert) of λ where
            (no _) → false
            (yes _) → true

      matchSerial : ∀{@0 bs} → Int bs → Bool
      matchSerial cserial =
        case _≋?_{A = Int} (Cert.getSerialInt cert) cserial of λ where
          (no ¬p) → false
          (yes p) → true

      helper₁ : List (Exists─ (List UInt8) RevokedCertificate)  →
                                Maybe (Exists─ (List UInt8) RevokedCertificate)
      helper₁ [] = nothing
      helper₁ (rv@(fst , mkTLV len (mkRevokedCertificateFields cserial rdate extn bs≡₁) len≡ bs≡) ∷ rest) =
        if matchSerial cserial ∧ matchCRLIssuerWithCertIssuer then (just rv) else helper₁ rest


      helper₂ : ∀{@0 bs} → List (Exists─ (List UInt8) RevokedCertificate) → Maybe (ExtensionFieldCertIssuer bs) →
                                Maybe (Exists─ (List UInt8) RevokedCertificate)
      helper₂ [] le = nothing
      helper₂ (rv@(fst , mkTLV len (mkRevokedCertificateFields cserial rdate none bs≡₁) len≡ bs≡) ∷ rest) le =
        if matchSerial cserial ∧ matchCRLIssuerWithCertIssuer then (just rv) else helper₂ rest le
      helper₂ (rv@(fst , mkTLV len (mkRevokedCertificateFields cserial rdate (some extn) bs≡₁) len≡ bs≡) ∷ rest) le =
        case EntryExtensions.getCertIssuer extn of λ where
          (─ .[] , none) →
            if matchSerial cserial ∧ matchCRLIssuerWithCertIssuer then (just rv) else helper₂ rest le
          (fst , some ci) →
            if matchSerial cserial ∧ (matchCertIssExtnWithCertIssuer ci ∨ matchCertIssExtnWithIAN ci)
              then (just rv)
            else
              helper₂ rest (just ci)
      
findCertStatus : Exists─ (List UInt8) RevokedCertificate → CertStatus
findCertStatus (fst , mkTLV len (mkRevokedCertificateFields cserial rdate none bs≡₁) len≡ bs≡) = unspecified
findCertStatus (fst , mkTLV len (mkRevokedCertificateFields cserial rdate (some extn) bs≡₁) len≡ bs≡) =
  case EntryExtensions.getReasonCode extn of λ where
          (_ , none) → unspecified
          (_ , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mk×ₚ (mkTLV len₁ val len≡₁ bs≡) sndₚ₁) len≡ refl) refl)) →
            case (Singleton.x ∘ IntegerValue.val) val of λ where
              (ℤ.+ 1) → keyCompromise
              (ℤ.+ 2) → cACompromise
              (ℤ.+ 3) → affiliationChanged
              (ℤ.+ 4) → superseded
              (ℤ.+ 5) → cessationOfOperation
              (ℤ.+ 6) → certificateHold
              (ℤ.+ 8) → removeFromCRL
              (ℤ.+ 9) → privilegeWithdrawn
              (ℤ.+ 10) → aACompromise
              _ → unspecified

-- Function to process revocation state
processRevocation : ∀{@0 bs} → RevInputs → DistPoint bs → State → State
processRevocation (mkRevInputs cert crl delta useDeltas) dp (mkState reasonsMask certstatus interimReasonsMask) =
  case scopeChecks of λ where
    true → stepK (revocationChecksCRL (revocationChecksDelta useDeltas delta (mkState reasonsMask certstatus computed_int_reason_mask)))
    false → (mkState reasonsMask UNDETERMINED interimReasonsMask)
  where
  computed_int_reason_mask = DcomputeIntReasonMask dp crl
  
  scopeChecks : Bool
  scopeChecks = (BscopeCompleteCRL cert dp crl) ∧
                (CscopeDeltaCRL useDeltas crl delta) ∧
                (EverifiyMask reasonsMask computed_int_reason_mask)

  revocationChecksDelta : ∀{@0 bs} → Bool → Maybe (CRL.CertList bs) → State → State
  revocationChecksDelta false _ st = st
  revocationChecksDelta true nothing st = st
  revocationChecksDelta true (just del) (mkState rm UNREVOKED irm) =
      case JfindSerialIssuerMatch cert del of λ where
          (just rv) →
            let
              cert_status = findCertStatus rv
            in
            (mkState (unonRevocationReason rm irm) cert_status irm)
          nothing → (mkState (unonRevocationReason rm irm) UNREVOKED irm)
  revocationChecksDelta true (just del) (mkState rm other_sts irm) =
      (mkState (unonRevocationReason rm irm) other_sts irm)
  
  revocationChecksCRL : State → State
  revocationChecksCRL (mkState rm UNREVOKED irm) =
        case JfindSerialIssuerMatch cert crl of λ where
          (just rv) →
            let
              cert_status = findCertStatus rv
            in
            (mkState (unonRevocationReason rm irm) cert_status irm)
          nothing → (mkState (unonRevocationReason rm irm) UNREVOKED irm)
  revocationChecksCRL (mkState rm other_sts irm) =
        (mkState (unonRevocationReason rm irm) other_sts irm)

  stepK : State → State
  stepK (mkState reasonsMask certStatus interimReasonsMask) =
    if certStatusEq certStatus removeFromCRL then
      (mkState reasonsMask UNREVOKED interimReasonsMask)
    else
      (mkState reasonsMask certStatus interimReasonsMask)

callProcessRevocation : RevInputs → CertStatus
callProcessRevocation ri@(mkRevInputs cert crl delta useDeltas) =
  case Cert.getCRLDIST cert of λ where
    (─ .[] , none) → UNDETERMINED
    (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mk×ₚ (cons x) sndₚ₁) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) → helper (cons x)
      where
      helper : ∀{@0 bs} → SequenceOf DistPoint bs → CertStatus
      helper nil = UNDETERMINED
      helper (cons (mkIListCons dp rest bs≡)) =
        case processRevocation ri dp initState of λ where
          st@(mkState reasonsMask₁ certStatus₁ interimReasonsMask₁) →
           case (findInList allReasons reasonsMask₁) of λ where
             true → certStatus₁
             false →
               case not (certStatusEq certStatus₁ UNREVOKED) of λ where
                 true → certStatus₁
                 false → helper₂ rest st
                   where
                   helper₂ : ∀{@0 bs} → SequenceOf DistPoint bs → State → CertStatus
                   helper₂ nil (mkState _ certStatus₂ _) = certStatus₂
                   helper₂ (cons (mkIListCons dp₂ rest₂ bs≡)) st₂@(mkState reasonsMask₂ certStatus₂ interimReasonsMask₂) =
                     case processRevocation ri dp₂ st₂ of λ where
                       st₃@(mkState reasonsMask₃ certStatus₃ interimReasonsMask₃) →
                         case (findInList allReasons reasonsMask₃) of λ where
                           true → certStatus₃
                           false →
                             case not (certStatusEq certStatus₃ UNREVOKED) of λ where
                               true → certStatus₃
                               false → helper₂ rest₂ st₃

-- callProcessRevocationSet : RevInputs → State → Set
-- callProcessRevocationSet ri (mkState [] UNREVOKED []) =
--   case callProcessRevocation ri of λ where
--     UNREVOKED → ⊥
--     _ → ⊤
-- callProcessRevocationSet ri (mkState _ _ _) = ⊥

-- callProcessRevocationSetDec : (ri : RevInputs) → (st : State) → Dec (callProcessRevocationSet ri st)
-- callProcessRevocationSetDec ri (mkState [] UNREVOKED []) =
--   case callProcessRevocation ri of λ where
--     UNREVOKED → no {!!}
--     _ → yes {!!}
-- callProcessRevocationSetDec ri (mkState _ _ _) = {!!}



-- -- case callProcessRevocation ri of λ where
--   --   UNREVOKED → {!!}
--   --   _ → {!!}


-- -- -- -- R1 : ∀ {@0 bs} → Cert bs → Set
-- -- -- -- R1 c = _≋_{A = SignAlg} (Cert.getTBSCertSignAlg c) (Cert.getCertSignAlg c)

-- -- -- -- r1 : ∀ {@0 bs} (c : Cert bs) → Dec (R1 c)
-- -- -- -- r1 c = Cert.getTBSCertSignAlg c ≋? Cert.getCertSignAlg c

-- -- processRevocation : ∀{@0 bs} → RevInputs → DistPoint bs → State → State


-- r1 : (ri : RevInputs) → (cs : CertStatus) → Dec {!!}
-- r1 = {!!} --Cert.getTBSCertSignAlg c ≋? Cert.getCertSignAlg c
