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
open import Armor.Data.X509.CRL.Semantic.Utils2
open import Armor.Data.X509.Extension.CRLDistPoint.DistPoint.TCB as DP
open import Armor.Data.X509.GeneralNames.GeneralName.TCB
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
open import Armor.Grammar.IList as IList
import      Armor.Grammar.Parallel.TCB
open import Armor.Prelude
open import Relation.Nullary.Implication

module Armor.Data.X509.CRL.Semantic.Validation2 where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8
open Armor.Grammar.Parallel.TCB UInt8


b1 : ∀{@0 bs₁ bs₂ bs₃} → Cert bs₁ → DistPoint bs₂ → CRL.CertList bs₃ → Set
b1 cert dp crl = (T (dpHasCrlissr dp) → T (crlIssuerMatchesDPcrlissuer dp crl ∧ indirectCRLtrue crl))
              ⊎ (T (not (dpHasCrlissr dp)) → T (crlIssuerMatchesCertIssuer cert crl))

b21 : ∀{@0 bs₂ bs₃} → DistPoint bs₂ → CRL.CertList bs₃ → Set                                    
b21 dp crl = (T (idpHasDPname crl ∧ dpHasDPname dp) → T (idpDpnameMatchesDPdpname dp crl))
                ⊎ (T (idpHasDPname crl ∧ not (dpHasDPname dp)) → T (idpDpnameMatchesDPcrlissuer dp crl))

b22 : ∀{@0 bs₁ bs₃} → Cert bs₁ → CRL.CertList bs₃ → Set
b22 cert crl = T (onlyUserCertstrue crl) → T (not (certIsCA cert))


b23 : ∀{@0 bs₁ bs₃} → Cert bs₁ → CRL.CertList bs₃ → Set
b23 cert crl = T (onlyCACertstrue crl) → T (certIsCA cert)


b24 : ∀{@0 bs₃} → CRL.CertList bs₃ → Set
b24 crl = T (not (onlyAttCertstrue crl))


b2 : ∀{@0 bs₁ bs₂ bs₃} → Cert bs₁ → DistPoint bs₂ → CRL.CertList bs₃ → Set
b2 cert dp crl = T (idpPresent crl) → (b21 dp crl × b22 cert crl × b23 cert crl × b24 crl)


BscopeCompleteCRL : ∀{@0 bs₁ bs₂ bs₃} → Cert bs₁ → DistPoint bs₂ → CRL.CertList bs₃ → Set
BscopeCompleteCRL cert dp crl = b1 cert dp crl × b2 cert dp crl


---------
b1? : ∀{@0 bs₁ bs₂ bs₃} → (cert : Cert bs₁) → (dp : DistPoint bs₂) → (crl : CRL.CertList bs₃) → Dec (b1 cert dp crl)
b1? cert dp crl = (T-dec →-dec T-dec) ⊎-dec (T-dec →-dec T-dec)


b21? : ∀{@0 bs₂ bs₃} → (dp : DistPoint bs₂) → (crl : CRL.CertList bs₃) → Dec (b21 dp crl)                                    
b21? dp crl = (T-dec →-dec T-dec) ⊎-dec (T-dec →-dec T-dec)


b22? : ∀{@0 bs₁ bs₃} → (cert : Cert bs₁) → (crl : CRL.CertList bs₃) → Dec (b22 cert crl)
b22? cert crl = T-dec →-dec T-dec


b23? : ∀{@0 bs₁ bs₃} → (cert : Cert bs₁) → (crl : CRL.CertList bs₃) → Dec (b23 cert crl)
b23? cert crl = T-dec →-dec T-dec


b24? : ∀{@0 bs₃} → (crl : CRL.CertList bs₃) → Dec (b24 crl)
b24? crl = T-dec


b2? : ∀{@0 bs₁ bs₂ bs₃} → (cert : Cert bs₁) → (dp : DistPoint bs₂) → (crl : CRL.CertList bs₃) → Dec (b2 cert dp crl)
b2? cert dp crl = T-dec →-dec (b21? dp crl ×-dec b22? cert crl ×-dec b23? cert crl ×-dec b24? crl)


bscopeCompleteCRL? : ∀{@0 bs₁ bs₂ bs₃} → (cert : Cert bs₁) → (dp : DistPoint bs₂) → (crl : CRL.CertList bs₃) → Dec (BscopeCompleteCRL cert dp crl)
bscopeCompleteCRL? cert dp crl = b1? cert dp crl ×-dec b2? cert dp crl
------------


c1 : ∀{@0 bs₁ bs₂} → CRL.CertList bs₁ → CRL.CertList bs₂ → Set
c1 crl delta = NameMatch (CRL.CertList.getIssuer crl) (CRL.CertList.getIssuer delta)


-- c2 : ∀{@0 bs₁ bs₂} → CRL.CertList bs₁ → CRL.CertList bs₂ → Set
-- c2 crl delta =
--   case (CRL.CertList.getIDP crl , CRL.CertList.getIDP delta) of λ where
--     ((─ .[] , none) , (─ .[] , none)) → ⊤
--     ((─ .[] , none) , (fst₁ , some x)) → ⊥
--     ((fst , some x) , (─ .[] , none)) → ⊥
--     ((fst , some x) , (fst₁ , some x₁)) → T (IdpMatch x x₁)


c3 : ∀{@0 bs₁ bs₂} → CRL.CertList bs₁ → CRL.CertList bs₂ → Set
c3 crl delta = T (AkiMatch crl delta)


CscopeDeltaCRL : ∀{@0 bs₁ bs₂} → CRL.CertList bs₁ → CRL.CertList bs₂ → Set
CscopeDeltaCRL crl delta = c1 crl delta × c3 crl delta


---------------------
c1? : ∀{@0 bs₁ bs₂} → (crl : CRL.CertList bs₁) → (delta : CRL.CertList bs₂) → Dec (c1 crl delta)
c1? crl delta = nameMatch? (CRL.CertList.getIssuer crl) (CRL.CertList.getIssuer delta)


-- c2? : ∀{@0 bs₁ bs₂} → (crl : CRL.CertList bs₁) → (delta : CRL.CertList bs₂) → Dec (c2 crl delta)
-- c2? crl delta =
--   case (CRL.CertList.getIDP crl , CRL.CertList.getIDP delta) of λ where
--     ((─ .[] , none) , (─ .[] , none)) → {!!}
--     ((─ .[] , none) , (fst₁ , some x)) → {!!}
--     ((fst , some x) , (─ .[] , none)) → {!!}
--     ((fst , some x) , (fst₁ , some x₁)) → {!!}


c3? : ∀{@0 bs₁ bs₂} → (crl : CRL.CertList bs₁) → (delta : CRL.CertList bs₂) → Dec (c3 crl delta)
c3? crl delta = T-dec


cscopeDeltaCRL? : ∀{@0 bs₁ bs₂} → (crl : CRL.CertList bs₁) → (delta : CRL.CertList bs₂) → Dec (CscopeDeltaCRL crl delta)
cscopeDeltaCRL? crl delta = c1? crl delta ×-dec c3? crl delta
-----------------------------------

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


EverifiyMask : List RevocationReason → List RevocationReason → Set
EverifiyMask reasonsMask interimReasonsMask = T (notFindInList' interimReasonsMask reasonsMask)


--------
everifiyMask? : (a : List RevocationReason) → (b : List RevocationReason) → Dec (EverifiyMask a b)
everifiyMask? a b = T-dec
-------


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


data ValidStateTransition {@0 bs} (ri : RevInputs) (dp : DistPoint bs): State → State → Set where

  fromUnrevokedToRevoked : ∀ {toRsn s₂}
    → toRsn ∈ (unspecified ∷ keyCompromise ∷ cACompromise ∷ affiliationChanged ∷ superseded
               ∷ cessationOfOperation ∷ certificateHold ∷ removeFromCRL ∷ privilegeWithdrawn ∷ aACompromise ∷ [ allReasons ])
    → (s₁ : State)
    → State.certStatus s₁ ≡ record { sts = UNREVOKED ; rsn = nothing }
    → State.certStatus s₂ ≡ record { sts = REVOKED ; rsn = just toRsn }
    → ValidStateTransition ri dp s₁ s₂

  fromRevokedToUnrevoked : ∀ {s₂}
    → (s₁ : State)
    → State.certStatus s₁ ≡ record { sts = REVOKED ; rsn = just removeFromCRL }
    → State.certStatus s₂ ≡ record { sts = UNREVOKED ; rsn = nothing }
    → ValidStateTransition ri dp s₁ s₂

  fromUnrevokedToUnrevoked : ∀ {s₂}
    → (s₁ : State)
    → State.certStatus s₁ ≡ record { sts = UNREVOKED ; rsn = nothing }
    → State.certStatus s₂ ≡ record { sts = UNREVOKED ; rsn = nothing }
    → ValidStateTransition ri dp s₁ s₂

  noTransition :
    (s₁ : State)
    → ValidStateTransition ri dp s₁ s₁


stateTransition : ∀{@0 bs} → (ri : RevInputs) → (dp : DistPoint bs) → (s₁ : State) → Σ[ s₂ ∈ State ] ValidStateTransition ri dp s₁ s₂
stateTransition (mkRevInputs cert crl (just delta) #1) dp s₁@(mkState reasonsMask record { sts = UNREVOKED ; rsn = (just rsn) }) =
  (s₁ , noTransition s₁)
stateTransition (mkRevInputs cert crl (just delta) #1) dp s₁@(mkState reasonsMask record { sts = UNREVOKED ; rsn = nothing }) =
  let
    temp₁ = (DcomputeIntReasonMask dp delta)
    temp₂ = (DcomputeIntReasonMask dp crl)
    temp = unonRevocationReason temp₁ temp₂
  in
  case bscopeCompleteCRL? cert dp crl of λ where
    (yes p) →
      case cscopeDeltaCRL? crl delta of λ where
        (yes r) →
          case (findStatus (JfindSerialIssuerMatch cert delta)) of λ where
            p@(record { sts = REVOKED ; rsn = just unspecified }) →
              let
                s₂ : State
                s₂ = mkState (unonRevocationReason reasonsMask temp₁) p
              in
              case everifiyMask? reasonsMask temp₁ of λ where
                (yes q) →
                  (s₂ , fromUnrevokedToRevoked (here refl) s₁ refl refl)
                (no ¬q) →
                  (s₁ , noTransition s₁)
            p@(record { sts = REVOKED ; rsn = just keyCompromise }) →
              let
                s₂ : State
                s₂ = mkState (unonRevocationReason reasonsMask temp₁) p
              in
              case everifiyMask? reasonsMask temp₁ of λ where
                (yes q) →
                  (s₂ , fromUnrevokedToRevoked (there (here refl)) s₁ refl refl)
                (no ¬q) →
                  (s₁ , noTransition s₁)
            p@(record { sts = REVOKED ; rsn = just cACompromise }) →
              let
                s₂ : State
                s₂ = mkState (unonRevocationReason reasonsMask temp₁) p
              in
              case everifiyMask? reasonsMask temp₁ of λ where
                (yes q) →
                  (s₂ , fromUnrevokedToRevoked (there (there (here refl))) s₁ refl refl)
                (no ¬q) →
                  (s₁ , noTransition s₁)
            p@(record { sts = REVOKED ; rsn = just affiliationChanged }) →
              let
                s₂ : State
                s₂ = mkState (unonRevocationReason reasonsMask temp₁) p
              in
              case everifiyMask? reasonsMask temp₁ of λ where
                (yes q) →
                  (s₂ , fromUnrevokedToRevoked (there (there (there (here refl)))) s₁ refl refl)
                (no ¬q) →
                  (s₁ , noTransition s₁)
            p@(record { sts = REVOKED ; rsn = just superseded }) →
              let
                s₂ : State
                s₂ = mkState (unonRevocationReason reasonsMask temp₁) p
              in
              case everifiyMask? reasonsMask temp₁ of λ where
                (yes q) →
                  (s₂ , fromUnrevokedToRevoked (there (there (there (there (here refl))))) s₁ refl refl)
                (no ¬q) →
                  (s₁ , noTransition s₁)
            p@(record { sts = REVOKED ; rsn = just cessationOfOperation }) →
              let
                s₂ : State
                s₂ = mkState (unonRevocationReason reasonsMask temp₁) p
              in
              case everifiyMask? reasonsMask temp₁ of λ where
                (yes q) →
                  (s₂ , fromUnrevokedToRevoked (there (there (there (there (there (here refl)))))) s₁ refl refl)
                (no ¬q) →
                  (s₁ , noTransition s₁)
            p@(record { sts = REVOKED ; rsn = just certificateHold }) →
              let
                s₂ : State
                s₂ = mkState (unonRevocationReason reasonsMask temp₁) p
              in
              case everifiyMask? reasonsMask temp₁ of λ where
                (yes q) →
                  (s₂ , fromUnrevokedToRevoked (there (there (there (there (there (there (here refl))))))) s₁ refl refl)
                (no ¬q) →
                  (s₁ , noTransition s₁)
            p@(record { sts = REVOKED ; rsn = just removeFromCRL }) →
              let
                s₂ : State
                s₂ = mkState (unonRevocationReason reasonsMask temp₁) p
              in
              case everifiyMask? reasonsMask temp₁ of λ where
                (yes q) →
                  (s₂ , fromUnrevokedToRevoked (there (there (there (there (there (there (there (here refl)))))))) s₁ refl refl)
                (no ¬q) →
                  (s₁ , noTransition s₁)
            p@(record { sts = REVOKED ; rsn = just privilegeWithdrawn }) →
              let
                s₂ : State
                s₂ = mkState (unonRevocationReason reasonsMask temp₁) p
              in
              case everifiyMask? reasonsMask temp₁ of λ where
                (yes q) →
                  (s₂ , fromUnrevokedToRevoked (there (there (there (there (there (there (there (there (here refl))))))))) s₁ refl refl)
                (no ¬q) →
                  (s₁ , noTransition s₁)
            p@(record { sts = REVOKED ; rsn = just aACompromise }) →
              let
                s₂ : State
                s₂ = mkState (unonRevocationReason reasonsMask temp₁) p
              in
              case everifiyMask? reasonsMask temp₁ of λ where
                (yes q) →
                  (s₂ , fromUnrevokedToRevoked (there (there (there (there (there (there (there (there (there (here refl)))))))))) s₁ refl refl)
                (no ¬q) →
                  (s₁ , noTransition s₁)
            p@(record { sts = REVOKED ; rsn = just allReasons }) →
              let
                s₂ : State
                s₂ = mkState (unonRevocationReason reasonsMask temp₁) p
              in
              case everifiyMask? reasonsMask temp₁ of λ where
                (yes q) →
                  (s₂ , fromUnrevokedToRevoked (there (there (there (there (there (there (there (there (there (there (here refl))))))))))) s₁ refl refl)
                (no ¬q) →
                  (s₁ , noTransition s₁)
            record { sts = REVOKED ; rsn = nothing } →
              (s₁ , noTransition s₁)
            record { sts = UNREVOKED ; rsn = (just rsn) } →
              (s₁ , noTransition s₁)
            record { sts = UNREVOKED ; rsn = nothing } →
              case (findStatus (JfindSerialIssuerMatch cert crl)) of λ where
                p@(record { sts = REVOKED ; rsn = just unspecified }) →
                  let
                    s₂ : State
                    s₂ = mkState (unonRevocationReason reasonsMask temp) p
                  in
                  case everifiyMask? reasonsMask temp of λ where
                    (yes q) →
                      (s₂ , fromUnrevokedToRevoked (here refl) s₁ refl refl)
                    (no ¬q) →
                      (s₁ , noTransition s₁)
                p@(record { sts = REVOKED ; rsn = just keyCompromise }) →
                  let
                    s₂ : State
                    s₂ = mkState (unonRevocationReason reasonsMask temp) p
                  in
                  case everifiyMask? reasonsMask temp of λ where
                    (yes q) →
                      (s₂ , fromUnrevokedToRevoked (there (here refl)) s₁ refl refl)
                    (no ¬q) →
                      (s₁ , noTransition s₁)
                p@(record { sts = REVOKED ; rsn = just cACompromise }) →
                  let
                    s₂ : State
                    s₂ = mkState (unonRevocationReason reasonsMask temp) p
                  in
                  case everifiyMask? reasonsMask temp of λ where
                    (yes q) →
                      (s₂ , fromUnrevokedToRevoked (there (there (here refl))) s₁ refl refl)
                    (no ¬q) →
                      (s₁ , noTransition s₁)
                p@(record { sts = REVOKED ; rsn = just affiliationChanged }) →
                  let
                    s₂ : State
                    s₂ = mkState (unonRevocationReason reasonsMask temp) p
                  in
                  case everifiyMask? reasonsMask temp of λ where
                    (yes q) →
                      (s₂ , fromUnrevokedToRevoked (there (there (there (here refl)))) s₁ refl refl)
                    (no ¬q) →
                      (s₁ , noTransition s₁)
                p@(record { sts = REVOKED ; rsn = just superseded }) →
                  let
                    s₂ : State
                    s₂ = mkState (unonRevocationReason reasonsMask temp) p
                  in
                  case everifiyMask? reasonsMask temp of λ where
                    (yes q) →
                      (s₂ , fromUnrevokedToRevoked (there (there (there (there (here refl))))) s₁ refl refl)
                    (no ¬q) →
                      (s₁ , noTransition s₁)
                p@(record { sts = REVOKED ; rsn = just cessationOfOperation }) →
                  let
                    s₂ : State
                    s₂ = mkState (unonRevocationReason reasonsMask temp) p
                  in
                  case everifiyMask? reasonsMask temp of λ where
                    (yes q) →
                      (s₂ , fromUnrevokedToRevoked (there (there (there (there (there (here refl)))))) s₁ refl refl)
                    (no ¬q) →
                      (s₁ , noTransition s₁)
                p@(record { sts = REVOKED ; rsn = just certificateHold }) →
                  let
                    s₂ : State
                    s₂ = mkState (unonRevocationReason reasonsMask temp) p
                  in
                  case everifiyMask? reasonsMask temp of λ where
                    (yes q) →
                      (s₂ , fromUnrevokedToRevoked (there (there (there (there (there (there (here refl))))))) s₁ refl refl)
                    (no ¬q) →
                      (s₁ , noTransition s₁)
                p@(record { sts = REVOKED ; rsn = just removeFromCRL }) →
                  let
                    s₂ : State
                    s₂ = mkState (unonRevocationReason reasonsMask temp) p
                  in
                  case everifiyMask? reasonsMask temp of λ where
                    (yes q) →
                      (s₂ , fromUnrevokedToRevoked (there (there (there (there (there (there (there (here refl)))))))) s₁ refl refl)
                    (no ¬q) →
                      (s₁ , noTransition s₁)
                p@(record { sts = REVOKED ; rsn = just privilegeWithdrawn }) →
                  let
                    s₂ : State
                    s₂ = mkState (unonRevocationReason reasonsMask temp) p
                  in
                  case everifiyMask? reasonsMask temp of λ where
                    (yes q) →
                      (s₂ , fromUnrevokedToRevoked (there (there (there (there (there (there (there (there (here refl))))))))) s₁ refl refl)
                    (no ¬q) →
                      (s₁ , noTransition s₁)
                p@(record { sts = REVOKED ; rsn = just aACompromise }) →
                  let
                    s₂ : State
                    s₂ = mkState (unonRevocationReason reasonsMask temp) p
                  in
                  case everifiyMask? reasonsMask temp of λ where
                    (yes q) →
                      (s₂ , fromUnrevokedToRevoked (there (there (there (there (there (there (there (there (there (here refl)))))))))) s₁ refl refl)
                    (no ¬q) →
                      (s₁ , noTransition s₁)
                p@(record { sts = REVOKED ; rsn = just allReasons }) →
                  let
                    s₂ : State
                    s₂ = mkState (unonRevocationReason reasonsMask temp) p
                  in
                  case everifiyMask? reasonsMask temp of λ where
                    (yes q) →
                      (s₂ , fromUnrevokedToRevoked (there (there (there (there (there (there (there (there (there (there (here refl))))))))))) s₁ refl refl)
                    (no ¬q) →
                      (s₁ , noTransition s₁)
                record { sts = REVOKED ; rsn = nothing } →
                  (s₁ , noTransition s₁)
                record { sts = UNREVOKED ; rsn = (just rsn) } →
                  (s₁ , noTransition s₁)
                p@record { sts = UNREVOKED ; rsn = nothing } →
                  let
                    s₂ : State
                    s₂ = mkState (unonRevocationReason reasonsMask temp) p
                  in
                  case everifiyMask? reasonsMask temp of λ where
                    (yes q) →
                      (s₂ , fromUnrevokedToUnrevoked s₁ refl refl)
                    (no ¬q) →
                      (s₁ , noTransition s₁)
        (no ¬r) →
          (s₁ , noTransition s₁)
    (no ¬p) →
      (s₁ , noTransition s₁)
stateTransition (mkRevInputs cert crl _ _) dp s₁@(mkState reasonsMask record { sts = REVOKED ; rsn = (just removeFromCRL) }) =
  ((mkState reasonsMask record { sts = UNREVOKED ; rsn = nothing }) , fromRevokedToUnrevoked s₁ refl refl)
stateTransition (mkRevInputs cert crl _ _) dp s₁@(mkState reasonsMask record { sts = REVOKED ; rsn = (just others) }) =
  (s₁ , noTransition s₁)
stateTransition (mkRevInputs cert crl _ _) dp s₁@(mkState reasonsMask record { sts = REVOKED ; rsn = nothing }) =
  (s₁ , noTransition s₁)
stateTransition (mkRevInputs cert crl _ _) dp s₁@(mkState reasonsMask record { sts = UNREVOKED ; rsn = (just rsn) }) =
  (s₁ , noTransition s₁)
stateTransition (mkRevInputs cert crl _ _) dp s₁@(mkState reasonsMask record { sts = UNREVOKED ; rsn = nothing }) =
  let
    temp₂ = (DcomputeIntReasonMask dp crl)
  in
  case bscopeCompleteCRL? cert dp crl of λ where
    (yes p) →
      case everifiyMask? reasonsMask temp₂ of λ where
        (yes q) →
          case (findStatus (JfindSerialIssuerMatch cert crl)) of λ where
            p@(record { sts = REVOKED ; rsn = just unspecified }) →
              let
                s₂ : State
                s₂ = mkState (unonRevocationReason reasonsMask temp₂) p
              in
              (s₂ , fromUnrevokedToRevoked (here refl) s₁ refl refl)
            p@(record { sts = REVOKED ; rsn = just keyCompromise }) →
              let
                s₂ : State
                s₂ = mkState (unonRevocationReason reasonsMask temp₂) p
              in
              (s₂ , fromUnrevokedToRevoked (there (here refl)) s₁ refl refl)
            p@(record { sts = REVOKED ; rsn = just cACompromise }) →
              let
                s₂ : State
                s₂ = mkState (unonRevocationReason reasonsMask temp₂) p
              in
              (s₂ , fromUnrevokedToRevoked (there (there (here refl))) s₁ refl refl)
            p@(record { sts = REVOKED ; rsn = just affiliationChanged }) →
              let
                s₂ : State
                s₂ = mkState (unonRevocationReason reasonsMask temp₂) p
              in
              (s₂ , fromUnrevokedToRevoked (there (there (there (here refl)))) s₁ refl refl)
            p@(record { sts = REVOKED ; rsn = just superseded }) →
              let
                s₂ : State
                s₂ = mkState (unonRevocationReason reasonsMask temp₂) p
              in
              (s₂ , fromUnrevokedToRevoked (there (there (there (there (here refl))))) s₁ refl refl)
            p@(record { sts = REVOKED ; rsn = just cessationOfOperation }) →
              let
                s₂ : State
                s₂ = mkState (unonRevocationReason reasonsMask temp₂) p
              in
              (s₂ , fromUnrevokedToRevoked (there (there (there (there (there (here refl)))))) s₁ refl refl)
            p@(record { sts = REVOKED ; rsn = just certificateHold }) →
              let
                s₂ : State
                s₂ = mkState (unonRevocationReason reasonsMask temp₂) p
              in
              (s₂ , fromUnrevokedToRevoked (there (there (there (there (there (there (here refl))))))) s₁ refl refl)
            p@(record { sts = REVOKED ; rsn = just removeFromCRL }) →
              let
                s₂ : State
                s₂ = mkState (unonRevocationReason reasonsMask temp₂) p
              in
              (s₂ , fromUnrevokedToRevoked (there (there (there (there (there (there (there (here refl)))))))) s₁ refl refl)
            p@(record { sts = REVOKED ; rsn = just privilegeWithdrawn }) →
              let
                s₂ : State
                s₂ = mkState (unonRevocationReason reasonsMask temp₂) p
              in
              (s₂ , fromUnrevokedToRevoked (there (there (there (there (there (there (there (there (here refl))))))))) s₁ refl refl)
            p@(record { sts = REVOKED ; rsn = just aACompromise }) →
              let
                s₂ : State
                s₂ = mkState (unonRevocationReason reasonsMask temp₂) p
              in
              (s₂ , fromUnrevokedToRevoked (there (there (there (there (there (there (there (there (there (here refl)))))))))) s₁ refl refl)
            p@(record { sts = REVOKED ; rsn = just allReasons }) →
              let
                s₂ : State
                s₂ = mkState (unonRevocationReason reasonsMask temp₂) p
              in
              (s₂ , fromUnrevokedToRevoked (there (there (there (there (there (there (there (there (there (there (here refl))))))))))) s₁ refl refl)
            record { sts = REVOKED ; rsn = nothing } →
              (s₁ , noTransition s₁)
            record { sts = UNREVOKED ; rsn = (just rsn) } →
              (s₁ , noTransition s₁)
            p@record { sts = UNREVOKED ; rsn = nothing } →
              let
                s₂ : State
                s₂ = mkState (unonRevocationReason reasonsMask temp₂) p
              in
              (s₂ , fromUnrevokedToUnrevoked s₁ refl refl)
        (no ¬q) →
          (s₁ , noTransition s₁)
    (no ¬p) →
      (s₁ , noTransition s₁)


data ProcessRevocation (ri : RevInputs) : List (Exists─ _ DistPoint) → State → State → Set where
  zeroStep : ∀{s} → ProcessRevocation ri [] s s
  oneStep : ∀ {@0 bs} (dp : DistPoint bs) (dps : List (Exists─ _ DistPoint)) (s₁ s₂ s₃ : State)
          → ValidStateTransition ri dp s₁ s₂
          → ProcessRevocation ri dps s₂ s₃ 
          → ProcessRevocation ri ((-, dp) ∷ dps) s₁ s₃


helper : (ri : RevInputs) → (dps : List (Exists─ _ DistPoint)) → (s₁ : State) → Σ[ s₂ ∈ State ] ProcessRevocation ri dps s₁ s₂
helper ri [] s₁ = (s₁ , zeroStep)
helper ri ((─ bs , dp) ∷ rest) s₁ = proj₁ rest,pf , foo
  where
  s₂,pf : Σ[ s₂ ∈ State ] ValidStateTransition ri dp s₁ s₂
  s₂,pf = stateTransition ri dp s₁

  rest,pf : Σ[ s₃ ∈ State ] ProcessRevocation ri rest (proj₁ s₂,pf) s₃
  rest,pf = helper ri rest (proj₁ s₂,pf)

  foo = oneStep dp rest s₁ (proj₁ s₂,pf) (proj₁ rest,pf) (proj₂ s₂,pf) (proj₂ rest,pf)


Main : RevInputs → String ⊎ Status
Main ri@(mkRevInputs cert crl delta useDeltas) =
  case Cert.getCRLDIST cert of λ where
    (─ .[] , none) → inj₁ "UNDETERMINED"
    (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mk×ₚ dps sndₚ₁) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) →
      let
        pr : Σ[ s ∈ State ] ProcessRevocation ri (toList _ dps) initState s 
        pr = helper ri (toList _ dps) initState
      in
      inj₂ (State.certStatus (proj₁ pr))
