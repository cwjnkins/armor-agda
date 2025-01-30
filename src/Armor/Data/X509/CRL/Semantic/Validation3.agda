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

open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

module Armor.Data.X509.CRL.Semantic.Validation3 where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8
open Armor.Grammar.Parallel.TCB UInt8

b1 : ∀{@0 bs₁ bs₂ bs₃} → Cert bs₁ → DistPoint bs₂ → CRL.CertList bs₃ → Bool
b1 cert dp crl =
  -- case dpHasCrlissr dp of λ where
  --   true →
  --     case crlIssuerMatchesDPcrlissuer dp crl of λ where
  --       true →
  --         case indirectCRLtrue crl of λ where
  --           true → true
  --           false → false
  --       false → false
  --   false →
      -- case crlIssuerMatchesCertIssuer cert crl of λ where
      --   true → true
      --   false → false
  case nameMatch? (Cert.getIssuer cert) (CRL.CertList.getIssuer crl) of λ where
    (no _) → false
    (yes _) → true


-- if (dpHasCrlissr dp) then (crlIssuerMatchesDPcrlissuer dp crl ∧ indirectCRLtrue crl)
--                  else (crlIssuerMatchesCertIssuer cert crl)


b21 : ∀{@0 bs₂ bs₃} → DistPoint bs₂ → CRL.CertList bs₃ → Bool                                    
b21 dp crl = if (idpHasDPname crl ∧ dpHasDPname dp) then (idpDpnameMatchesDPdpname dp crl)
             else
               if (idpHasDPname crl ∧ not (dpHasDPname dp)) then (idpDpnameMatchesDPcrlissuer dp crl)
               else true


b22 : ∀{@0 bs₁ bs₃} → Cert bs₁ → CRL.CertList bs₃ → Bool
b22 cert crl = if (onlyUserCertstrue crl) then (not (certIsCA cert)) else true


b23 : ∀{@0 bs₁ bs₃} → Cert bs₁ → CRL.CertList bs₃ → Bool
b23 cert crl = if (onlyCACertstrue crl) then (certIsCA cert) else true


b24 : ∀{@0 bs₃} → CRL.CertList bs₃ → Bool
b24 crl = (not (onlyAttCertstrue crl))


b2 : ∀{@0 bs₁ bs₂ bs₃} → Cert bs₁ → DistPoint bs₂ → CRL.CertList bs₃ → Bool
b2 cert dp crl = if (idpPresent crl) then (b21 dp crl ∧ b22 cert crl ∧ b23 cert crl ∧ b24 crl) else true
  
BscopeCompleteCRL : ∀{@0 bs₁ bs₂ bs₃} → Cert bs₁ → DistPoint bs₂ → CRL.CertList bs₃ → Bool
BscopeCompleteCRL cert dp crl = b1 cert dp crl -- ∧ b2 cert dp crl




BscopeCompleteCRLDec : ∀{@0 bs₁ bs₂ bs₃} → (cert : Cert bs₁) → (dp : DistPoint bs₂) → (crl : CRL.CertList bs₃) → Dec (T (BscopeCompleteCRL cert dp crl))
BscopeCompleteCRLDec cert dp crl = {!!} --b1 cert dp crl ∧ b2 cert dp crl


CscopeDeltaCRL : ∀{@0 bs₁ bs₂} → CRL.CertList bs₁ → CRL.CertList bs₂ → Bool
CscopeDeltaCRL crl delta = c1 ∧ c2 ∧ c3
  where
    c1 : Bool
    c1 = case nameMatch? (CRL.CertList.getIssuer crl) (CRL.CertList.getIssuer delta) of λ where
      (yes _) → true
      (no _) → false

    c2 : Bool
    c2 =
      case CRL.CertList.getIDP crl of λ where
        (_ , none) →
          case CRL.CertList.getIDP delta of λ where
            (_ , none) → true
            (_ , some y) → false
        (_ , some crlidp) →
          case CRL.CertList.getIDP delta of λ where
            (_ , none) → false
            (_ , some deltaidp) → {!!} --idpMatch? crlidp deltaidp

    c3 : Bool
    c3 = {!!} --akiMatch? crl delta


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


data ValidStateTransition {@0 bs₁} (ri : RevInputs) (dp : DistPoint bs₁) : State → State → Set where

  fromUnrevokedToRsnDelta : ∀ {delta toRsn s₂}
    → (toRsn ≡ unspecified ⊎ toRsn ≡ keyCompromise ⊎ toRsn ≡ cACompromise ⊎ toRsn ≡ affiliationChanged ⊎ toRsn ≡ superseded
       ⊎ toRsn ≡ cessationOfOperation ⊎ toRsn ≡ certificateHold ⊎ toRsn ≡ privilegeWithdrawn ⊎ toRsn ≡ aACompromise)
    → (s₁ : State)
    → State.certStatus s₁ ≡ UNREVOKED
    → T (RevInputs.useDeltas ri) × (RevInputs.delta ri) ≡ (just delta)
    → (BscopeCompleteCRL (RevInputs.cert ri) dp (RevInputs.crl ri)
      ∧ CscopeDeltaCRL (RevInputs.crl ri) delta) ≡ true
    → (let
        temp₁ = (DcomputeIntReasonMask dp delta)
        temp₂ = (DcomputeIntReasonMask dp (RevInputs.crl ri))
        temp = unonRevocationReason temp₁ temp₂
      in
      (findCertStatus (JfindSerialIssuerMatch (RevInputs.cert ri) delta) ≡ toRsn
       × EverifiyMask (State.reasonsMask s₁) temp₁ ≡ true
       × State.reasonsMask s₂ ≡ (unonRevocationReason (State.reasonsMask s₁) temp₁)
       × State.certStatus s₂ ≡ toRsn)
      ⊎
      (findCertStatus (JfindSerialIssuerMatch (RevInputs.cert ri) delta) ≡ UNREVOKED
       × findCertStatus (JfindSerialIssuerMatch (RevInputs.cert ri) (RevInputs.crl ri)) ≡ toRsn
       × EverifiyMask (State.reasonsMask s₁) temp ≡ true
       × State.reasonsMask s₂ ≡ (unonRevocationReason (State.reasonsMask s₁) temp)
       × State.certStatus s₂ ≡ toRsn))
    → ValidStateTransition ri dp s₁ s₂

  fromUnrevokedToUnrevokedDelta : ∀ {delta toRsn s₂}
    → (toRsn ≡ UNREVOKED)
    → (s₁ : State)
    → State.certStatus s₁ ≡ UNREVOKED
    → T (RevInputs.useDeltas ri) × (RevInputs.delta ri) ≡ (just delta)
    → (BscopeCompleteCRL (RevInputs.cert ri) dp (RevInputs.crl ri)
      ∧ CscopeDeltaCRL (RevInputs.crl ri) delta) ≡ true
    → (let
        temp₁ = (DcomputeIntReasonMask dp delta)
        temp₂ = (DcomputeIntReasonMask dp (RevInputs.crl ri))
        temp = unonRevocationReason temp₁ temp₂
      in
      (findCertStatus (JfindSerialIssuerMatch (RevInputs.cert ri) delta) ≡ removeFromCRL
       × EverifiyMask (State.reasonsMask s₁) temp₁ ≡ true
       × State.reasonsMask s₂ ≡ (unonRevocationReason (State.reasonsMask s₁) temp₁)
       × State.certStatus s₂ ≡ toRsn)
      ⊎
      (findCertStatus (JfindSerialIssuerMatch (RevInputs.cert ri) delta) ≡ UNREVOKED
       × findCertStatus (JfindSerialIssuerMatch (RevInputs.cert ri) (RevInputs.crl ri)) ≡ removeFromCRL
       × EverifiyMask (State.reasonsMask s₁) temp ≡ true
       × State.reasonsMask s₂ ≡ (unonRevocationReason (State.reasonsMask s₁) temp)
       × State.certStatus s₂ ≡ toRsn)
      ⊎
      (findCertStatus (JfindSerialIssuerMatch (RevInputs.cert ri) delta) ≡ UNREVOKED
       × findCertStatus (JfindSerialIssuerMatch (RevInputs.cert ri) (RevInputs.crl ri)) ≡ UNREVOKED
       × EverifiyMask (State.reasonsMask s₁) temp ≡ true
       × State.reasonsMask s₂ ≡ (unonRevocationReason (State.reasonsMask s₁) temp)
       × State.certStatus s₂ ≡ toRsn))
    → ValidStateTransition ri dp s₁ s₂

  fromUnrevokedToRsnComplete : ∀ {toRsn s₂}
    → (toRsn ≡ unspecified ⊎ toRsn ≡ keyCompromise ⊎ toRsn ≡ cACompromise ⊎ toRsn ≡ affiliationChanged ⊎ toRsn ≡ superseded
       ⊎ toRsn ≡ cessationOfOperation ⊎ toRsn ≡ certificateHold ⊎ toRsn ≡ privilegeWithdrawn ⊎ toRsn ≡ aACompromise)
    → (s₁ : State)
    → State.certStatus s₁ ≡ UNREVOKED
    → BscopeCompleteCRL (RevInputs.cert ri) dp (RevInputs.crl ri) ≡ true
    → (let
        temp = (DcomputeIntReasonMask dp (RevInputs.crl ri))
      in
      (findCertStatus (JfindSerialIssuerMatch (RevInputs.cert ri) (RevInputs.crl ri)) ≡ toRsn
       × EverifiyMask (State.reasonsMask s₁) temp ≡ true
       × State.reasonsMask s₂ ≡ (unonRevocationReason (State.reasonsMask s₁) temp)
       × State.certStatus s₂ ≡ toRsn))
    → ValidStateTransition ri dp s₁ s₂

  fromUnrevokedToUnrevokedComplete : ∀ {toRsn s₂}
    → (toRsn ≡ UNREVOKED)
    → (s₁ : State)
    → State.certStatus s₁ ≡ UNREVOKED
    → BscopeCompleteCRL (RevInputs.cert ri) dp (RevInputs.crl ri) ≡ true
    → (let
        temp = (DcomputeIntReasonMask dp (RevInputs.crl ri))
      in
      (findCertStatus (JfindSerialIssuerMatch (RevInputs.cert ri) (RevInputs.crl ri)) ≡ removeFromCRL
       × EverifiyMask (State.reasonsMask s₁) temp ≡ true
       × State.reasonsMask s₂ ≡ (unonRevocationReason (State.reasonsMask s₁) temp)
       × State.certStatus s₂ ≡ toRsn)
      ⊎
      (findCertStatus (JfindSerialIssuerMatch (RevInputs.cert ri) (RevInputs.crl ri)) ≡ UNREVOKED
       × EverifiyMask (State.reasonsMask s₁) temp ≡ true
       × State.reasonsMask s₂ ≡ (unonRevocationReason (State.reasonsMask s₁) temp)
       × State.certStatus s₂ ≡ toRsn))
    → ValidStateTransition ri dp s₁ s₂

  noTransition : --needs more guard
    (s₁ : State)
    → ValidStateTransition ri dp s₁ s₁


ScopeProof₁ : ∀{@0 bs₁ bs₂ bs₃ bs₄} → (cert : Cert bs₁) → (dp : DistPoint bs₂) → (crl : CRL.CertList bs₃) → (delta : CRL.CertList bs₄) 
                  → (BscopeCompleteCRL cert dp crl ∧ CscopeDeltaCRL crl delta) ≡ true
ScopeProof₁ = {!!}


ScopeProof₂ : ∀{@0 bs₁ bs₂ bs₃} → (cert : Cert bs₁) → (dp : DistPoint bs₂) → (crl : CRL.CertList bs₃)
                  → BscopeCompleteCRL cert dp crl ≡ true
ScopeProof₂ cert dp crl = {!!}

ScopeProof₃ : ∀{@0 bs₁ bs₂ bs₃} → (cert : Cert bs₁) → (dp : DistPoint bs₂) → (crl : CRL.CertList bs₃) →
                  Dec (BscopeCompleteCRL cert dp crl ≡ true)
ScopeProof₃ cert dp crl =  
  case  BscopeCompleteCRL cert dp crl of λ where
    true → yes {!!}
    false → {!!}


stateTransition : ∀{@0 bs} → (ri : RevInputs) → (dp : DistPoint bs) → (s₁ : State) → Σ[ s₂ ∈ State ] ValidStateTransition ri dp s₁ s₂
stateTransition ri@(mkRevInputs cert crl (just delta) true) dp s₁@(mkState reasonsMask UNREVOKED) =
  let
    temp₁ = (DcomputeIntReasonMask dp delta)
    temp₂ = (DcomputeIntReasonMask dp crl)
    temp = unonRevocationReason temp₁ temp₂
  in
  case (findCertStatus (JfindSerialIssuerMatch cert delta) , findCertStatus (JfindSerialIssuerMatch cert crl)) of λ where
    (unspecified , _) →
      let
        s₂ : State
        s₂ = mkState (unonRevocationReason (State.reasonsMask s₁) temp₁) unspecified
      in
      (s₂ , fromUnrevokedToRsnDelta (inj₁ refl) s₁ refl (tt , refl) (ScopeProof₁ cert dp crl delta) {!!})
    (keyCompromise , _) →
      let
        s₂ : State
        s₂ = mkState (unonRevocationReason (State.reasonsMask s₁) temp₁) keyCompromise
      in
      (s₂ , fromUnrevokedToRsnDelta (inj₂ (inj₁ refl)) s₁ refl (tt , refl) (ScopeProof₁ cert dp crl delta) {!!})
    (cACompromise , _) →
      let
        s₂ : State
        s₂ = mkState (unonRevocationReason (State.reasonsMask s₁) temp₁) cACompromise
      in
      (s₂ , fromUnrevokedToRsnDelta (inj₂ (inj₂ (inj₁ refl))) s₁ refl (tt , refl) (ScopeProof₁ cert dp crl delta) {!!})
    (affiliationChanged , _) →
      let
        s₂ : State
        s₂ = mkState (unonRevocationReason (State.reasonsMask s₁) temp₁) affiliationChanged
      in
      (s₂ , fromUnrevokedToRsnDelta (inj₂ (inj₂ (inj₂ (inj₁ refl)))) s₁ refl (tt , refl) (ScopeProof₁ cert dp crl delta) {!!})
    (superseded , _) →
      let
        s₂ : State
        s₂ = mkState (unonRevocationReason (State.reasonsMask s₁) temp₁) superseded
      in
      (s₂ , fromUnrevokedToRsnDelta (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ refl))))) s₁ refl (tt , refl) (ScopeProof₁ cert dp crl delta) {!!})
    (cessationOfOperation , _) →
      let
        s₂ : State
        s₂ = mkState (unonRevocationReason (State.reasonsMask s₁) temp₁) cessationOfOperation
      in
      (s₂ , fromUnrevokedToRsnDelta (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ refl)))))) s₁ refl (tt , refl) (ScopeProof₁ cert dp crl delta) {!!})
    (certificateHold , _) →
      let
        s₂ : State
        s₂ = mkState (unonRevocationReason (State.reasonsMask s₁) temp₁) certificateHold
      in
      (s₂ , fromUnrevokedToRsnDelta (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ refl))))))) s₁ refl (tt , refl) (ScopeProof₁ cert dp crl delta) {!!})
    (removeFromCRL , _) →
      let
        s₂ : State
        s₂ = mkState (unonRevocationReason (State.reasonsMask s₁) temp₁) UNREVOKED
      in
      (s₂ , fromUnrevokedToUnrevokedDelta  refl s₁ refl (tt , refl) (ScopeProof₁ cert dp crl delta) {!!})
    (privilegeWithdrawn , _) →
      let
        s₂ : State
        s₂ = mkState (unonRevocationReason (State.reasonsMask s₁) temp₁) privilegeWithdrawn
      in
      (s₂ , fromUnrevokedToRsnDelta (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ refl)))))))) s₁ refl (tt , refl) (ScopeProof₁ cert dp crl delta) {!!})
    (aACompromise , _) →
      let
        s₂ : State
        s₂ = mkState (unonRevocationReason (State.reasonsMask s₁) temp₁) aACompromise
      in
      (s₂ , fromUnrevokedToRsnDelta (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ refl)))))))) s₁ refl (tt , refl) (ScopeProof₁ cert dp crl delta) {!!})
    (UNREVOKED , unspecified) →
      let
        s₂ : State
        s₂ = mkState (unonRevocationReason (State.reasonsMask s₁) temp) unspecified
      in
      (s₂ , fromUnrevokedToRsnDelta (inj₁ refl) s₁ refl (tt , refl) (ScopeProof₁ cert dp crl delta) {!!})
    (UNREVOKED , keyCompromise) →
      let
        s₂ : State
        s₂ = mkState (unonRevocationReason (State.reasonsMask s₁) temp) keyCompromise
      in
      (s₂ , fromUnrevokedToRsnDelta (inj₂ (inj₁ refl)) s₁ refl (tt , refl) (ScopeProof₁ cert dp crl delta) {!!})
    (UNREVOKED , cACompromise) →
      let
        s₂ : State
        s₂ = mkState (unonRevocationReason (State.reasonsMask s₁) temp) cACompromise
      in
      (s₂ , fromUnrevokedToRsnDelta (inj₂ (inj₂ (inj₁ refl))) s₁ refl (tt , refl) (ScopeProof₁ cert dp crl delta) {!!})
    (UNREVOKED , affiliationChanged) →
      let
        s₂ : State
        s₂ = mkState (unonRevocationReason (State.reasonsMask s₁) temp) affiliationChanged
      in
      (s₂ , fromUnrevokedToRsnDelta (inj₂ (inj₂ (inj₂ (inj₁ refl)))) s₁ refl (tt , refl) (ScopeProof₁ cert dp crl delta) {!!})
    (UNREVOKED , superseded) →
      let
        s₂ : State
        s₂ = mkState (unonRevocationReason (State.reasonsMask s₁) temp) superseded
      in
      (s₂ , fromUnrevokedToRsnDelta (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ refl))))) s₁ refl (tt , refl) (ScopeProof₁ cert dp crl delta) {!!})
    (UNREVOKED , cessationOfOperation) →
      let
        s₂ : State
        s₂ = mkState (unonRevocationReason (State.reasonsMask s₁) temp) cessationOfOperation
      in
      (s₂ , fromUnrevokedToRsnDelta (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ refl)))))) s₁ refl (tt , refl) (ScopeProof₁ cert dp crl delta) {!!})
    (UNREVOKED , certificateHold) →
      let
        s₂ : State
        s₂ = mkState (unonRevocationReason (State.reasonsMask s₁) temp) certificateHold
      in
      (s₂ , fromUnrevokedToRsnDelta (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ refl))))))) s₁ refl (tt , refl) (ScopeProof₁ cert dp crl delta) {!!})
    (UNREVOKED , removeFromCRL) →
      let
        s₂ : State
        s₂ = mkState (unonRevocationReason (State.reasonsMask s₁) temp) UNREVOKED
      in
      (s₂ , fromUnrevokedToUnrevokedDelta  refl s₁ refl (tt , refl) (ScopeProof₁ cert dp crl delta) {!!})
    (UNREVOKED , privilegeWithdrawn) →
      let
        s₂ : State
        s₂ = mkState (unonRevocationReason (State.reasonsMask s₁) temp) privilegeWithdrawn
      in
      (s₂ , fromUnrevokedToRsnDelta (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ refl)))))))) s₁ refl (tt , refl) (ScopeProof₁ cert dp crl delta) {!!})
    (UNREVOKED , aACompromise) →
      let
        s₂ : State
        s₂ = mkState (unonRevocationReason (State.reasonsMask s₁) temp) aACompromise
      in
      (s₂ , fromUnrevokedToRsnDelta (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ refl)))))))) s₁ refl (tt , refl) (ScopeProof₁ cert dp crl delta) {!!})
    (UNREVOKED , UNREVOKED) →
      let
        s₂ : State
        s₂ = mkState (unonRevocationReason (State.reasonsMask s₁) temp) UNREVOKED
      in
      (s₂ , fromUnrevokedToUnrevokedDelta  refl s₁ refl (tt , refl) (ScopeProof₁ cert dp crl delta) {!!})
    (_ , _) → (s₁ , noTransition s₁)
stateTransition ri@(mkRevInputs cert crl _ _) dp s₁@(mkState reasonsMask UNREVOKED) =
  let
    temp₂ = (DcomputeIntReasonMask dp crl)
  in
  case (findCertStatus (JfindSerialIssuerMatch cert crl)) of λ where
    (unspecified) →
      let
        s₂ : State
        s₂ = mkState (unonRevocationReason (State.reasonsMask s₁) temp₂) unspecified
      in
      (case BscopeCompleteCRL cert dp crl of λ where
        true →
          (case EverifiyMask (State.reasonsMask s₁) temp₂ of λ where
            true → (s₂ , fromUnrevokedToRsnComplete (inj₁ refl) s₁ refl (toWitness{Q = {!!}} tt) {!!})
            false → {!!})
        false → {!!})
      -- (s₂ , fromUnrevokedToRsnComplete (inj₁ refl) s₁ refl {!!} {!!})
    (keyCompromise) →
      let
        s₂ : State
        s₂ = mkState (unonRevocationReason (State.reasonsMask s₁) temp₂) keyCompromise
      in
      (s₂ , fromUnrevokedToRsnComplete (inj₂ (inj₁ refl)) s₁ refl (ScopeProof₂ cert dp crl) {!!})
    (cACompromise) →
      let
        s₂ : State
        s₂ = mkState (unonRevocationReason (State.reasonsMask s₁) temp₂) cACompromise
      in
      (s₂ , fromUnrevokedToRsnComplete (inj₂ (inj₂ (inj₁ refl))) s₁ refl (ScopeProof₂ cert dp crl) {!!})
    (affiliationChanged) →
      let
        s₂ : State
        s₂ = mkState (unonRevocationReason (State.reasonsMask s₁) temp₂) affiliationChanged
      in
      (s₂ , fromUnrevokedToRsnComplete (inj₂ (inj₂ (inj₂ (inj₁ refl)))) s₁ refl (ScopeProof₂ cert dp crl) {!!})
    (superseded) →
      let
        s₂ : State
        s₂ = mkState (unonRevocationReason (State.reasonsMask s₁) temp₂) superseded
      in
      (s₂ , fromUnrevokedToRsnComplete (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ refl))))) s₁ refl (ScopeProof₂ cert dp crl) {!!})
    (cessationOfOperation) →
      let
        s₂ : State
        s₂ = mkState (unonRevocationReason (State.reasonsMask s₁) temp₂) cessationOfOperation
      in
      (s₂ , fromUnrevokedToRsnComplete (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ refl)))))) s₁ refl (ScopeProof₂ cert dp crl) {!!})
    (certificateHold) →
      let
        s₂ : State
        s₂ = mkState (unonRevocationReason (State.reasonsMask s₁) temp₂) certificateHold
      in
      (s₂ , fromUnrevokedToRsnComplete (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ refl))))))) s₁ refl (ScopeProof₂ cert dp crl) {!!})
    (removeFromCRL) →
      let
        s₂ : State
        s₂ = mkState (unonRevocationReason (State.reasonsMask s₁) temp₂) UNREVOKED
      in
      (s₂ , fromUnrevokedToUnrevokedComplete  refl s₁ refl {!!} {!!})
    (privilegeWithdrawn) →
      let
        s₂ : State
        s₂ = mkState (unonRevocationReason (State.reasonsMask s₁) temp₂) privilegeWithdrawn
      in
      (s₂ , fromUnrevokedToRsnComplete (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ refl)))))))) s₁ refl (ScopeProof₂ cert dp crl) {!!})
    (aACompromise) →
      let
        s₂ : State
        s₂ = mkState (unonRevocationReason (State.reasonsMask s₁) temp₂) aACompromise
      in
      (s₂ , fromUnrevokedToRsnComplete (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ refl)))))))) s₁ refl (ScopeProof₂ cert dp crl) {!!})
    (UNREVOKED) →
      let
        s₂ : State
        s₂ = mkState (unonRevocationReason (State.reasonsMask s₁) temp₂) UNREVOKED
      in
      (s₂ , fromUnrevokedToUnrevokedComplete refl s₁ refl {!!} {!!})
    (_) → (s₁ , noTransition s₁)
stateTransition ri dp s₁@(mkState reasonsMask _) = (s₁ , noTransition s₁)


-- data ProcessRevocation (ri : RevInputs) : List (Exists─ _ DistPoint) → State → State → Set where
--   zeroStep : ∀{s} → ProcessRevocation ri [] s s
--   oneStep : ∀ {@0 bs} (dp : DistPoint bs) (dps : List (Exists─ _ DistPoint)) (s₁ s₂ s₃ : State)
--           → ValidStateTransition ri dp s₁ s₂
--           → ProcessRevocation ri dps s₂ s₃ 
--           → ProcessRevocation ri ((-, dp) ∷ dps) s₁ s₃


-- helper : (ri : RevInputs) → (dps : List (Exists─ _ DistPoint)) → (s₁ : State) → Σ[ s₂ ∈ State ] ProcessRevocation ri dps s₁ s₂
-- helper ri [] s₁ = (s₁ , zeroStep)
-- helper ri ((─ bs , dp) ∷ rest) s₁ = proj₁ rest,pf , foo
--   where
--   s₂,pf : Σ[ s₂ ∈ State ] ValidStateTransition ri dp s₁ s₂
--   s₂,pf = stateTransition ri dp s₁

--   rest,pf : Σ[ s₃ ∈ State ] ProcessRevocation ri rest (proj₁ s₂,pf) s₃
--   rest,pf = helper ri rest (proj₁ s₂,pf)

--   foo = oneStep dp rest s₁ (proj₁ s₂,pf) (proj₁ rest,pf) (proj₂ s₂,pf) (proj₂ rest,pf)


-- Main : RevInputs → CertStatus
-- Main ri@(mkRevInputs cert crl delta useDeltas _) =
--   case Cert.getCRLDIST cert of λ where
--     (─ .[] , none) → UNDETERMINED
--     (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mk×ₚ dps sndₚ₁) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) →
--       let
--         pr : Σ[ s ∈ State ] ProcessRevocation ri (toList _ dps) initState s 
--         pr = helper ri (toList _ dps) initState
--       in
--       State.certStatus (proj₁ pr)
