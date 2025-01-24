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
            (_ , none) → akiMatch crl delta
            (_ , some y) → false
        (_ , some crlidp) →
          case CRL.CertList.getIDP delta of λ where
            (_ , none) → false
            (_ , some deltaidp) → idpMatch crlidp deltaidp ∧ akiMatch crl delta 


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


EverifiyMask : List RevocationReason → List RevocationReason → Bool
EverifiyMask reasonsMask interimReasonsMask = notFindInList' interimReasonsMask reasonsMask


JfindSerialIssuerMatch : ∀{@0 bs₁ bs₂} → Cert bs₁ → CRL.CertList bs₂ → Maybe (Exists─ (List UInt8) RevokedCertificate)
JfindSerialIssuerMatch cert crl =
  case CRL.CertList.getRevokedCertificateList crl of λ where
    v → if indirectCRLtrue crl then (helper₂{[]} v nothing) else helper₁ v
      where
      helper₁ : List (Exists─ (List UInt8) RevokedCertificate)  →
                                Maybe (Exists─ (List UInt8) RevokedCertificate)
      helper₁ [] = nothing
      helper₁ (rv@(fst , mkTLV len (mkRevokedCertificateFields cserial rdate extn bs≡₁) len≡ bs≡) ∷ rest) =
        if matchSerial cserial cert ∧ matchCRLIssuerWithCertIssuer crl cert then (just rv) else helper₁ rest


      helper₂ : ∀{@0 bs} → List (Exists─ (List UInt8) RevokedCertificate) → Maybe (ExtensionFieldCertIssuer bs) →
                                Maybe (Exists─ (List UInt8) RevokedCertificate)
      helper₂ [] le = nothing
      helper₂ (rv@(fst , mkTLV len (mkRevokedCertificateFields cserial rdate none bs≡₁) len≡ bs≡) ∷ rest) le =
        if matchSerial cserial cert ∧ matchCRLIssuerWithCertIssuer crl cert then (just rv) else helper₂ rest le
      helper₂ (rv@(fst , mkTLV len (mkRevokedCertificateFields cserial rdate (some extn) bs≡₁) len≡ bs≡) ∷ rest) le =
        case EntryExtensions.getCertIssuer extn of λ where
          (─ .[] , none) →
            if matchSerial cserial cert ∧ matchCRLIssuerWithCertIssuer crl cert then (just rv) else helper₂ rest le
          (fst , some ci) →
            if matchSerial cserial cert ∧ (matchCertIssExtnWithCertIssuer ci cert ∨ matchCertIssExtnWithIAN ci cert)
              then (just rv)
            else
              helper₂ rest (just ci)


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
