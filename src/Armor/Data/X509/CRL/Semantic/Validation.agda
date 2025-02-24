{-# OPTIONS --erasure --sized-types #-}

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
open import Armor.Data.X509.Semantic.Chain.TCB
open import Armor.Data.X509.Semantic.Chain
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
open import Armor.Grammar.IList as IList
import      Armor.Grammar.Parallel.TCB
open import Armor.Prelude

module Armor.Data.X509.CRL.Semantic.Validation where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8
open Armor.Grammar.Parallel.TCB UInt8


b1 : ∀{@0 bs₁ bs₂ bs₃} → (c : Cert bs₁) → (dp : DistPoint bs₂) → (Dp∈Cert c dp ≡ true) → (crl : CRL.CertList bs₃) → (isDeltaCRL crl ≡ false) → Set
b1 cert dp eq crl eq₁ = (T (dpHasCrlissr dp) → T (crlIssuerMatchesDPcrlissuer dp crl ∧ indirectCRLtrue crl))
                   × (T (not (dpHasCrlissr dp)) → T (crlIssuerMatchesCertIssuer cert crl))

b21 : ∀{@0 bs₂ bs₃} → DistPoint bs₂ → CRL.CertList bs₃ → Set                                    
b21 dp crl = (T (idpHasDPname crl ∧ dpHasDPname dp) → T (idpDpnameMatchesDPdpname dp crl))
                × (T (idpHasDPname crl ∧ not (dpHasDPname dp)) → T (idpDpnameMatchesDPcrlissuer dp crl))

b22 : ∀{@0 bs₁ bs₃} → Cert bs₁ → CRL.CertList bs₃ → Set
b22 cert crl = T (onlyUserCertstrue crl) → T (not (certIsCA cert))


b23 : ∀{@0 bs₁ bs₃} → Cert bs₁ → CRL.CertList bs₃ → Set
b23 cert crl = T (onlyCACertstrue crl) → T (certIsCA cert)


b24 : ∀{@0 bs₃} → CRL.CertList bs₃ → Set
b24 crl = T (not (onlyAttCertstrue crl))


b2 : ∀{@0 bs₁ bs₂ bs₃} → (c : Cert bs₁) → (dp : DistPoint bs₂) → (Dp∈Cert c dp ≡ true) → (crl : CRL.CertList bs₃) → (isDeltaCRL crl ≡ false) → Set
b2 cert dp eq crl eq₁ = T (idpPresent crl) → (b21 dp crl × b22 cert crl × b23 cert crl × b24 crl)


BscopeCompleteCRL : ∀{@0 bs₁ bs₂ bs₃} → (c : Cert bs₁) → (dp : DistPoint bs₂) → (Dp∈Cert c dp ≡ true) → (crl : CRL.CertList bs₃) → (isDeltaCRL crl ≡ false) → Set
BscopeCompleteCRL cert dp eq crl eq₁ = b1 cert dp eq crl eq₁ × b2 cert dp eq crl eq₁

---------
b1? : ∀{@0 bs₁ bs₂ bs₃} → (cert : Cert bs₁) → (dp : DistPoint bs₂) → (eq : Dp∈Cert cert dp ≡ true) → (crl : CRL.CertList bs₃) → (eq₁ : isDeltaCRL crl ≡ false) → Dec (b1 cert dp eq crl eq₁)
b1? cert dp eq crl eq₁ = (T-dec →-dec T-dec) ×-dec (T-dec →-dec T-dec)


b21? : ∀{@0 bs₂ bs₃} → (dp : DistPoint bs₂) → (crl : CRL.CertList bs₃) → Dec (b21 dp crl)                                    
b21? dp crl = (T-dec →-dec T-dec) ×-dec (T-dec →-dec T-dec)


b22? : ∀{@0 bs₁ bs₃} → (cert : Cert bs₁) → (crl : CRL.CertList bs₃) → Dec (b22 cert crl)
b22? cert crl = T-dec →-dec T-dec


b23? : ∀{@0 bs₁ bs₃} → (cert : Cert bs₁) → (crl : CRL.CertList bs₃) → Dec (b23 cert crl)
b23? cert crl = T-dec →-dec T-dec


b24? : ∀{@0 bs₃} → (crl : CRL.CertList bs₃) → Dec (b24 crl)
b24? crl = T-dec


b2? : ∀{@0 bs₁ bs₂ bs₃} → (cert : Cert bs₁) → (dp : DistPoint bs₂) → (eq : Dp∈Cert cert dp ≡ true) → (crl : CRL.CertList bs₃) → (eq₁ : isDeltaCRL crl ≡ false) → Dec (b2 cert dp eq crl eq₁)
b2? cert dp eq crl eq₁ = T-dec →-dec (b21? dp crl ×-dec b22? cert crl ×-dec b23? cert crl ×-dec b24? crl)


bscopeCompleteCRL? : ∀{@0 bs₁ bs₂ bs₃} → (cert : Cert bs₁) → (dp : DistPoint bs₂) → (eq : Dp∈Cert cert dp ≡ true) → (crl : CRL.CertList bs₃) → (eq₁ : isDeltaCRL crl ≡ false) → Dec (BscopeCompleteCRL cert dp eq crl eq₁)
bscopeCompleteCRL? cert dp eq crl eq₁ = b1? cert dp eq crl eq₁ ×-dec b2? cert dp eq crl eq₁

-- ------------

c1 : ∀{@0 bs₁ bs₂} → (crl : CRL.CertList bs₁) → (delta : CRL.CertList bs₂) → (eq₁ : isDeltaCRL crl ≡ false) → (eq₂ : isDeltaCRL delta ≡ true) → Set
c1 crl delta eq₁ eq₂ = NameMatch (CRL.CertList.getIssuer crl) (CRL.CertList.getIssuer delta)

c2-helper : (x₁ x₂ : Exists─ (List UInt8) (Option ExtensionFieldIDP)) → Set
c2-helper (─ _ , none) (─ _ , none) = ⊤
c2-helper (─ _ , none) (_ , some x) = ⊥
c2-helper (_ , some x) (─ _ , none) = ⊥
c2-helper (_ , some x₁) (_ , some x₂) = T (IdpMatch x₁ x₂)

c2 : ∀{@0 bs₁ bs₂} → (crl : CRL.CertList bs₁) → (delta : CRL.CertList bs₂) → (eq₁ : isDeltaCRL crl ≡ false) → (eq₂ : isDeltaCRL delta ≡ true) → Set
c2 crl delta eq₁ eq₂ = c2-helper (CRL.CertList.getIDP crl) (CRL.CertList.getIDP delta)

c3 : ∀{@0 bs₁ bs₂} → (crl : CRL.CertList bs₁) → (delta : CRL.CertList bs₂) → (eq₁ : isDeltaCRL crl ≡ false) → (eq₂ : isDeltaCRL delta ≡ true) → Set
c3 crl delta eq₁ eq₂ = T (AkiMatch crl delta)


CscopeDeltaCRL : ∀{@0 bs₁ bs₂} → (crl : CRL.CertList bs₁) → (delta : CRL.CertList bs₂) → (eq₁ : isDeltaCRL crl ≡ false) → (eq₂ : isDeltaCRL delta ≡ true) → Set
CscopeDeltaCRL crl delta eq₁ eq₂ = c1 crl delta eq₁ eq₂ × c2 crl delta eq₁ eq₂ × c3 crl delta eq₁ eq₂

---------------------
c1? : ∀{@0 bs₁ bs₂} → (crl : CRL.CertList bs₁) → (delta : CRL.CertList bs₂) → (eq₁ : isDeltaCRL crl ≡ false) → (eq₂ : isDeltaCRL delta ≡ true) → Dec (c1 crl delta eq₁ eq₂)
c1? crl delta eq₁ eq₂ = nameMatch? (CRL.CertList.getIssuer crl) (CRL.CertList.getIssuer delta)

c2-helper? : (x₁ x₂ : Exists─ (List UInt8) (Option ExtensionFieldIDP)) → Dec (c2-helper x₁ x₂)
c2-helper? (─ _ , none) (─ _ , none) = yes tt
c2-helper? (─ _ , none) (_ , some x) = no λ ()
c2-helper? (_ , some x) (─ _ , none) = no λ ()
c2-helper? (_ , some x₁) (_ , some x₂) = T-dec

c2? : ∀{@0 bs₁ bs₂} → (crl : CRL.CertList bs₁) → (delta : CRL.CertList bs₂) → (eq₁ : isDeltaCRL crl ≡ false) → (eq₂ : isDeltaCRL delta ≡ true) → Dec (c2 crl delta eq₁ eq₂)
c2? crl delta eq₁ eq₂ = c2-helper? (CRL.CertList.getIDP crl) (CRL.CertList.getIDP delta)

c3? : ∀{@0 bs₁ bs₂} → (crl : CRL.CertList bs₁) → (delta : CRL.CertList bs₂) → (eq₁ : isDeltaCRL crl ≡ false) → (eq₂ : isDeltaCRL delta ≡ true) → Dec (c3 crl delta eq₁ eq₂)
c3? crl delta eq₁ eq₂ = T-dec

cscopeDeltaCRL? : ∀{@0 bs₁ bs₂} → (crl : CRL.CertList bs₁) → (delta : CRL.CertList bs₂) → (eq₁ : isDeltaCRL crl ≡ false) → (eq₂ : isDeltaCRL delta ≡ true) → Dec (CscopeDeltaCRL crl delta eq₁ eq₂)
cscopeDeltaCRL? crl delta eq₁ eq₂ = c1? crl delta eq₁ eq₂ ×-dec c2? crl delta eq₁ eq₂ ×-dec c3? crl delta eq₁ eq₂
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
--------

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

data ValidStateTransition {@0 bs} (ri : RevInputs) (dp : DistPoint bs): ValidRevocationState → ValidRevocationState → Set where

  fromUnrevokedToRevoked₁ : ∀ {toRsn s₂ rm}
    → toRsn ∈ (unspecified ∷ keyCompromise ∷ cACompromise ∷ affiliationChanged ∷ superseded
               ∷ cessationOfOperation ∷ certificateHold ∷ privilegeWithdrawn ∷ aACompromise ∷ [ allReasons ])
    → (s₁ : ValidRevocationState)
    → s₁ ≡ UNREVOKED rm
    → (pf₁ : Dp∈Cert (RevInputs.cert ri) dp ≡ true)
    → (pf₂ : isDeltaCRL (RevInputs.crl ri) ≡ false)
    → BscopeCompleteCRL (RevInputs.cert ri) dp pf₁ (RevInputs.crl ri) pf₂
    → T (certStatusEq (findStatus (JfindSerialIssuerMatch (RevInputs.cert ri) (RevInputs.crl ri))) (REVOKED [] toRsn))
    → let
      intmask = DcomputeIntReasonMask dp (RevInputs.crl ri)
      in
      (EverifiyMask rm intmask ×
       s₂ ≡ REVOKED (unonRevocationReason rm intmask) toRsn)
    → ValidStateTransition ri dp s₁ s₂

  fromUnrevokedToRevoked₂ : ∀ {toRsn s₂ delta rm}
    → toRsn ∈ (unspecified ∷ keyCompromise ∷ cACompromise ∷ affiliationChanged ∷ superseded
               ∷ cessationOfOperation ∷ certificateHold ∷ privilegeWithdrawn ∷ aACompromise ∷ [ allReasons ])
    → (s₁ : ValidRevocationState)
    → s₁ ≡ UNREVOKED rm
    → (just delta) ≡ (RevInputs.delta ri)
    → (pf₁ : Dp∈Cert (RevInputs.cert ri) dp ≡ true)
    → (pf₂ : isDeltaCRL (RevInputs.crl ri) ≡ false)
    → (pf₃ : isDeltaCRL delta ≡ true)
    → BscopeCompleteCRL (RevInputs.cert ri) dp pf₁ (RevInputs.crl ri) pf₂
    → CscopeDeltaCRL (RevInputs.crl ri) delta pf₂ pf₃
    → T (certStatusEq (findStatus (JfindSerialIssuerMatch (RevInputs.cert ri) delta)) (REVOKED [] toRsn))
    → let
      intmask = DcomputeIntReasonMask dp delta
      in
      (EverifiyMask rm intmask ×
       s₂ ≡ REVOKED (unonRevocationReason rm intmask) toRsn)
    → ValidStateTransition ri dp s₁ s₂

  fromUnrevokedToRevoked₃ : ∀ {toRsn s₂ delta rm}
    → toRsn ∈ (unspecified ∷ keyCompromise ∷ cACompromise ∷ affiliationChanged ∷ superseded
               ∷ cessationOfOperation ∷ certificateHold ∷ privilegeWithdrawn ∷ aACompromise ∷ [ allReasons ])
    → (s₁ : ValidRevocationState)
    → s₁ ≡ UNREVOKED rm
    → (just delta) ≡ (RevInputs.delta ri)
    → (pf₁ : Dp∈Cert (RevInputs.cert ri) dp ≡ true)
    → (pf₂ : isDeltaCRL (RevInputs.crl ri) ≡ false)
    → (pf₃ : isDeltaCRL delta ≡ true)
    → BscopeCompleteCRL (RevInputs.cert ri) dp pf₁ (RevInputs.crl ri) pf₂
    → CscopeDeltaCRL (RevInputs.crl ri) delta pf₂ pf₃
    → ¬ T (certStatusEq (findStatus (JfindSerialIssuerMatch (RevInputs.cert ri) delta)) (REVOKED [] toRsn))
    → T (certStatusEq (findStatus (JfindSerialIssuerMatch (RevInputs.cert ri) (RevInputs.crl ri))) (REVOKED [] toRsn))
    → let
      intmask₁ = DcomputeIntReasonMask dp delta
      intmask₂ = DcomputeIntReasonMask dp (RevInputs.crl ri)
      intmask = unonRevocationReason intmask₁ intmask₂
      in
      (EverifiyMask rm intmask ×
       s₂ ≡ REVOKED (unonRevocationReason rm intmask) toRsn)
    → ValidStateTransition ri dp s₁ s₂

  fromUnrevokedToUnrevoked₁₁ : ∀ {s₂ rm}
    → (s₁ : ValidRevocationState)
    → s₁ ≡ UNREVOKED rm
    → (pf₁ : Dp∈Cert (RevInputs.cert ri) dp ≡ true)
    → (pf₂ : isDeltaCRL (RevInputs.crl ri) ≡ false)
    → BscopeCompleteCRL (RevInputs.cert ri) dp pf₁ (RevInputs.crl ri) pf₂
    → T (certStatusEq (findStatus (JfindSerialIssuerMatch (RevInputs.cert ri) (RevInputs.crl ri))) (REVOKED [] removeFromCRL))
    → let
      intmask = DcomputeIntReasonMask dp (RevInputs.crl ri)
      in
      (EverifiyMask rm intmask ×
       s₂ ≡ UNREVOKED (unonRevocationReason rm intmask))
    → ValidStateTransition ri dp s₁ s₂

  fromUnrevokedToUnrevoked₁₂ : ∀ {s₂ delta rm}
    → (s₁ : ValidRevocationState)
    → s₁ ≡ UNREVOKED rm
    → (just delta) ≡ (RevInputs.delta ri)
    → (pf₁ : Dp∈Cert (RevInputs.cert ri) dp ≡ true)
    → (pf₂ : isDeltaCRL (RevInputs.crl ri) ≡ false)
    → (pf₃ : isDeltaCRL delta ≡ true)
    → BscopeCompleteCRL (RevInputs.cert ri) dp pf₁ (RevInputs.crl ri) pf₂
    → CscopeDeltaCRL (RevInputs.crl ri) delta pf₂ pf₃
    → T (certStatusEq (findStatus (JfindSerialIssuerMatch (RevInputs.cert ri) delta)) (REVOKED [] removeFromCRL))
    → let
      intmask = DcomputeIntReasonMask dp delta
      in
      (EverifiyMask rm intmask ×
       s₂ ≡ UNREVOKED (unonRevocationReason rm intmask))
    → ValidStateTransition ri dp s₁ s₂

  fromUnrevokedToUnrevoked₁₃ : ∀ {s₂ delta rm}
    → (s₁ : ValidRevocationState)
    → s₁ ≡ UNREVOKED rm
    → (just delta) ≡ (RevInputs.delta ri)
    → (pf₁ : Dp∈Cert (RevInputs.cert ri) dp ≡ true)
    → (pf₂ : isDeltaCRL (RevInputs.crl ri) ≡ false)
    → (pf₃ : isDeltaCRL delta ≡ true)
    → BscopeCompleteCRL (RevInputs.cert ri) dp pf₁ (RevInputs.crl ri) pf₂
    → CscopeDeltaCRL (RevInputs.crl ri) delta pf₂ pf₃
    → ¬ T (certStatusEq (findStatus (JfindSerialIssuerMatch (RevInputs.cert ri) delta)) (REVOKED [] removeFromCRL))
    → T (certStatusEq (findStatus (JfindSerialIssuerMatch (RevInputs.cert ri) (RevInputs.crl ri))) (REVOKED [] removeFromCRL))
    → let
      intmask₁ = DcomputeIntReasonMask dp delta
      intmask₂ = DcomputeIntReasonMask dp (RevInputs.crl ri)
      intmask = unonRevocationReason intmask₁ intmask₂
      in
      (EverifiyMask rm intmask ×
       s₂ ≡ UNREVOKED (unonRevocationReason rm intmask))
    → ValidStateTransition ri dp s₁ s₂
    
  fromUnrevokedToUnrevoked₂ : ∀ {s₂ rm}
    → (s₁ : ValidRevocationState)
    → s₁ ≡ UNREVOKED rm
    → (pf₁ : Dp∈Cert (RevInputs.cert ri) dp ≡ true)
    → (pf₂ : isDeltaCRL (RevInputs.crl ri) ≡ false)
    → ¬ BscopeCompleteCRL (RevInputs.cert ri) dp pf₁ (RevInputs.crl ri) pf₂
    → s₂ ≡ UNREVOKED rm
    → ValidStateTransition ri dp s₁ s₂
  
  fromUnrevokedToUnrevoked₃ : ∀ {s₂ delta rm}
    → (s₁ : ValidRevocationState)
    → s₁ ≡ UNREVOKED rm
    → (just delta) ≡ (RevInputs.delta ri)
    → (pf₂ : isDeltaCRL (RevInputs.crl ri) ≡ false)
    → (pf₃ : isDeltaCRL delta ≡ true)
    → ¬ CscopeDeltaCRL (RevInputs.crl ri) delta pf₂ pf₃
    → s₂ ≡ UNREVOKED rm
    → ValidStateTransition ri dp s₁ s₂

  fromUnrevokedToUnrevoked₄₁ : ∀ {s₂ rm}
    → (s₁ : ValidRevocationState)
    → s₁ ≡ UNREVOKED rm
    → (pf₂ : isDeltaCRL (RevInputs.crl ri) ≡ false)
    → let
      intmask = DcomputeIntReasonMask dp (RevInputs.crl ri)
      in
      ¬ EverifiyMask rm intmask
    → s₂ ≡ UNREVOKED (unonRevocationReason rm intmask)
    → ValidStateTransition ri dp s₁ s₂

  fromUnrevokedToUnrevoked₄₂ : ∀ {s₂ delta rm}
    → (s₁ : ValidRevocationState)
    → s₁ ≡ UNREVOKED rm
    → (just delta) ≡ (RevInputs.delta ri)
    → (pf₂ : isDeltaCRL (RevInputs.crl ri) ≡ false)
    → (pf₃ : isDeltaCRL delta ≡ true)
    → let
      intmask₁ = (DcomputeIntReasonMask dp delta)
      in
      ¬ EverifiyMask rm intmask₁
    → s₂ ≡ UNREVOKED (unonRevocationReason rm intmask₁)
    → ValidStateTransition ri dp s₁ s₂

  fromUnrevokedToUnrevoked₄₃ : ∀ {s₂ delta rm}
    → (s₁ : ValidRevocationState)
    → s₁ ≡ UNREVOKED rm
    → (just delta) ≡ (RevInputs.delta ri)
    → (pf₂ : isDeltaCRL (RevInputs.crl ri) ≡ false)
    → (pf₃ : isDeltaCRL delta ≡ true)
    → let
      intmask₁ = (DcomputeIntReasonMask dp delta)
      intmask₂ = (DcomputeIntReasonMask dp (RevInputs.crl ri))
      intmask = unonRevocationReason intmask₁ intmask₂
      in
      ¬ EverifiyMask rm intmask
    → s₂ ≡ UNREVOKED (unonRevocationReason rm intmask)
    → ValidStateTransition ri dp s₁ s₂

  fromUnrevokedToUnrevoked₅ : ∀ {s₂ toRsn delta rm₁ rm₂}
    → (s₁ : ValidRevocationState)
    → s₁ ≡ UNREVOKED rm₁
    → (just delta) ≡ (RevInputs.delta ri)
    → ¬ T (certStatusEq (findStatus (JfindSerialIssuerMatch (RevInputs.cert ri) delta)) (REVOKED [] toRsn))
    → ¬ T (certStatusEq (findStatus (JfindSerialIssuerMatch (RevInputs.cert ri) (RevInputs.crl ri))) (REVOKED [] toRsn))
    → s₂ ≡ UNREVOKED rm₂
    → ValidStateTransition ri dp s₁ s₂

  fromUnrevokedToUnrevoked₆ : ∀ {s₂ toRsn rm₁ rm₂}
    → (s₁ : ValidRevocationState)
    → s₁ ≡ UNREVOKED rm₁
    → ¬ T (certStatusEq (findStatus (JfindSerialIssuerMatch (RevInputs.cert ri) (RevInputs.crl ri))) (REVOKED [] toRsn))
    → s₂ ≡ UNREVOKED rm₂
    → ValidStateTransition ri dp s₁ s₂

  fromUnrevokedToUnrevoked₇ : ∀ {s₂ rm}
    → (s₁ : ValidRevocationState)
    → s₁ ≡ UNREVOKED rm
    → (¬pf₁ : ¬ Dp∈Cert (RevInputs.cert ri) dp ≡ true)
    → s₂ ≡ UNREVOKED rm
    → ValidStateTransition ri dp s₁ s₂

  fromUnrevokedToUnrevoked₈ : ∀ {s₂ rm}
    → (s₁ : ValidRevocationState)
    → s₁ ≡ UNREVOKED rm
    → (¬pf₂ : ¬ isDeltaCRL (RevInputs.crl ri) ≡ false)
    → s₂ ≡ UNREVOKED rm
    → ValidStateTransition ri dp s₁ s₂

  fromUnrevokedToUnrevoked₉ : ∀ {s₂ delta rm}
    → (s₁ : ValidRevocationState)
    → s₁ ≡ UNREVOKED rm
    → (just delta) ≡ (RevInputs.delta ri)
    → (¬pf₃ : ¬ isDeltaCRL delta ≡ true)
    → s₂ ≡ UNREVOKED rm
    → ValidStateTransition ri dp s₁ s₂

  fromRevoked : ∀ {x rm}
    → (s₁ : ValidRevocationState)
    → s₁ ≡ REVOKED rm x
    → ValidStateTransition ri dp s₁ s₁
  
validStateTransition : ∀{@0 bs} → (ri : RevInputs) → (dp : DistPoint bs) → (s₁ : ValidRevocationState) → Σ[ s₂ ∈ ValidRevocationState ] ValidStateTransition ri dp s₁ s₂
validStateTransition (mkRevInputs cert crl delta) dp s₁@(REVOKED reasonsMask x) = s₁ , fromRevoked s₁ refl
validStateTransition (mkRevInputs cert crl (just delta)) dp s₁@(UNREVOKED reasonsMask) =
  let
    temp₁ = (DcomputeIntReasonMask dp delta)
    temp₂ = (DcomputeIntReasonMask dp crl)
    temp = unonRevocationReason temp₁ temp₂
  in
  case (_≟_ (Dp∈Cert cert dp) true) ,′e (_≟_ (isDeltaCRL crl) false) ,′e (_≟_ (isDeltaCRL delta) true) of λ where
    (yes p , yes p₁ , yes p₅) →
      case (bscopeCompleteCRL? cert dp p crl p₁) ,′e (cscopeDeltaCRL? crl delta p₁ p₅)  of λ where
          (yes p₂ , yes p₄) →
            case certStatusEq? (findStatus (JfindSerialIssuerMatch cert delta)) (REVOKED [] unspecified)
                 ,′e certStatusEq? (findStatus (JfindSerialIssuerMatch cert crl)) (REVOKED [] unspecified) of λ where
              (yes a₁ , _) →
                case everifiyMask? reasonsMask temp₁ of λ where
                  (yes p₃) → ((REVOKED (unonRevocationReason reasonsMask temp₁) unspecified)) ,
                             fromUnrevokedToRevoked₂ (here refl) s₁ refl refl p p₁ p₅ p₂ p₄ a₁ (p₃ , refl)
                  (no ¬p₃) → UNREVOKED (unonRevocationReason reasonsMask temp₁) ,
                             fromUnrevokedToUnrevoked₄₂ s₁ refl refl p₁ p₅ ¬p₃ refl
              (no ¬a₁ , yes a₂) →
                case everifiyMask? reasonsMask temp of λ where
                  (yes p₃) → REVOKED (unonRevocationReason reasonsMask temp) unspecified ,
                             fromUnrevokedToRevoked₃ (here refl) s₁ refl refl p p₁ p₅ p₂ p₄ ¬a₁ a₂ (p₃ , refl)
                  (no ¬p₃) → UNREVOKED (unonRevocationReason reasonsMask temp) ,
                             fromUnrevokedToUnrevoked₄₃ s₁ refl refl p₁ p₅ ¬p₃ refl
              (no ¬a₁ , no ¬a₂) →
                case certStatusEq? (findStatus (JfindSerialIssuerMatch cert delta)) (REVOKED [] keyCompromise)
                  ,′e certStatusEq? (findStatus (JfindSerialIssuerMatch cert crl)) (REVOKED [] keyCompromise) of λ where
                  (yes b₁ , _) →
                    case everifiyMask? reasonsMask temp₁ of λ where
                      (yes p₃) → ((REVOKED (unonRevocationReason reasonsMask temp₁) keyCompromise)) ,
                                 fromUnrevokedToRevoked₂ (there (here refl)) s₁ refl refl p p₁ p₅ p₂ p₄ b₁ (p₃ , refl)
                      (no ¬p₃) → UNREVOKED (unonRevocationReason reasonsMask temp₁) ,
                                 fromUnrevokedToUnrevoked₄₂ s₁ refl refl p₁ p₅ ¬p₃ refl
                  (no ¬b₁ , yes b₂) →
                    case everifiyMask? reasonsMask temp of λ where
                      (yes p₃) → REVOKED (unonRevocationReason reasonsMask temp) keyCompromise ,
                                 fromUnrevokedToRevoked₃ (there (here refl)) s₁ refl refl p p₁ p₅ p₂ p₄ ¬b₁ b₂ (p₃ , refl)
                      (no ¬p₃) → UNREVOKED (unonRevocationReason reasonsMask temp) ,
                                 fromUnrevokedToUnrevoked₄₃ s₁ refl refl p₁ p₅ ¬p₃ refl
                  (no ¬b₁ , no ¬b₂) → 
                    case certStatusEq? (findStatus (JfindSerialIssuerMatch cert delta)) (REVOKED [] cACompromise)
                      ,′e certStatusEq? (findStatus (JfindSerialIssuerMatch cert crl)) (REVOKED [] cACompromise) of λ where
                      (yes c₁ , _) →
                        case everifiyMask? reasonsMask temp₁ of λ where
                          (yes p₃) → ((REVOKED (unonRevocationReason reasonsMask temp₁) cACompromise)) ,
                                     fromUnrevokedToRevoked₂ (there (there (here refl))) s₁ refl refl p p₁ p₅ p₂ p₄ c₁ (p₃ , refl)
                          (no ¬p₃) → UNREVOKED (unonRevocationReason reasonsMask temp₁) ,
                                     fromUnrevokedToUnrevoked₄₂ s₁ refl refl p₁ p₅ ¬p₃ refl
                      (no ¬c₁ , yes c₂) →
                        case everifiyMask? reasonsMask temp of λ where
                          (yes p₃) → REVOKED (unonRevocationReason reasonsMask temp) cACompromise ,
                                     fromUnrevokedToRevoked₃ (there (there (here refl))) s₁ refl refl p p₁ p₅ p₂ p₄ ¬c₁ c₂ (p₃ , refl)
                          (no ¬p₃) → UNREVOKED (unonRevocationReason reasonsMask temp) ,
                                     fromUnrevokedToUnrevoked₄₃ s₁ refl refl p₁ p₅ ¬p₃ refl
                      (no ¬c₁ , no ¬c₂) → 
                        case certStatusEq? (findStatus (JfindSerialIssuerMatch cert delta)) (REVOKED [] affiliationChanged)
                          ,′e certStatusEq? (findStatus (JfindSerialIssuerMatch cert crl)) (REVOKED [] affiliationChanged) of λ where
                          (yes d₁ , _) →
                            case everifiyMask? reasonsMask temp₁ of λ where
                              (yes p₃) → ((REVOKED (unonRevocationReason reasonsMask temp₁) affiliationChanged)) ,
                                         fromUnrevokedToRevoked₂ (there (there (there (here refl)))) s₁ refl refl p p₁ p₅ p₂ p₄ d₁ (p₃ , refl)
                              (no ¬p₃) → UNREVOKED (unonRevocationReason reasonsMask temp₁) ,
                                         fromUnrevokedToUnrevoked₄₂ s₁ refl refl p₁ p₅ ¬p₃ refl
                          (no ¬d₁ , yes d₂) →
                            case everifiyMask? reasonsMask temp of λ where
                              (yes p₃) → ((REVOKED (unonRevocationReason reasonsMask temp) affiliationChanged)) ,
                                         fromUnrevokedToRevoked₃ (there (there (there (here refl)))) s₁ refl refl p p₁ p₅ p₂ p₄ ¬d₁ d₂ (p₃ , refl)
                              (no ¬p₃) → UNREVOKED (unonRevocationReason reasonsMask temp) ,
                                         fromUnrevokedToUnrevoked₄₃ s₁ refl refl p₁ p₅ ¬p₃ refl
                          (no ¬d₁ , no ¬d₂) → 
                            case certStatusEq? (findStatus (JfindSerialIssuerMatch cert delta)) (REVOKED [] superseded)
                              ,′e certStatusEq? (findStatus (JfindSerialIssuerMatch cert crl)) (REVOKED [] superseded) of λ where
                              (yes e₁ , _) →
                                case everifiyMask? reasonsMask temp₁ of λ where
                                  (yes p₃) → ((REVOKED (unonRevocationReason reasonsMask temp₁) superseded)) ,
                                             fromUnrevokedToRevoked₂ (there (there (there (there (here refl))))) s₁ refl refl p p₁ p₅ p₂ p₄ e₁ (p₃ , refl)
                                  (no ¬p₃) → UNREVOKED (unonRevocationReason reasonsMask temp₁) ,
                                             fromUnrevokedToUnrevoked₄₂ s₁ refl refl p₁ p₅ ¬p₃ refl
                              (no ¬e₁ , yes e₂) →
                                case everifiyMask? reasonsMask temp of λ where
                                  (yes p₃) → ((REVOKED (unonRevocationReason reasonsMask temp) superseded)) ,
                                             fromUnrevokedToRevoked₃ (there (there (there (there (here refl))))) s₁ refl refl p p₁ p₅ p₂ p₄ ¬e₁ e₂ (p₃ , refl)
                                  (no ¬p₃) → UNREVOKED (unonRevocationReason reasonsMask temp) ,
                                             fromUnrevokedToUnrevoked₄₃ s₁ refl refl p₁ p₅ ¬p₃ refl
                              (no ¬e₁ , no ¬e₂) → 
                                case certStatusEq? (findStatus (JfindSerialIssuerMatch cert delta)) (REVOKED [] cessationOfOperation)
                                  ,′e certStatusEq? (findStatus (JfindSerialIssuerMatch cert crl)) (REVOKED [] cessationOfOperation) of λ where
                                  (yes f₁ , _) →
                                    case everifiyMask? reasonsMask temp₁ of λ where
                                      (yes p₃) → ((REVOKED (unonRevocationReason reasonsMask temp₁) cessationOfOperation)) ,
                                                 fromUnrevokedToRevoked₂ (there (there (there (there (there (here refl)))))) s₁ refl refl p p₁ p₅ p₂ p₄ f₁ (p₃ , refl)
                                      (no ¬p₃) → UNREVOKED (unonRevocationReason reasonsMask temp₁) ,
                                                 fromUnrevokedToUnrevoked₄₂ s₁ refl refl p₁ p₅ ¬p₃ refl
                                  (no ¬f₁ , yes f₂) →
                                    case everifiyMask? reasonsMask temp of λ where
                                      (yes p₃) → ((REVOKED (unonRevocationReason reasonsMask temp) cessationOfOperation)) ,
                                                 fromUnrevokedToRevoked₃ (there (there (there (there (there (here refl)))))) s₁ refl refl p p₁ p₅ p₂ p₄ ¬f₁ f₂ (p₃ , refl)
                                      (no ¬p₃) → UNREVOKED (unonRevocationReason reasonsMask temp) ,
                                                 fromUnrevokedToUnrevoked₄₃ s₁ refl refl p₁ p₅ ¬p₃ refl
                                  (no ¬f₁ , no ¬f₂) → 
                                    case certStatusEq? (findStatus (JfindSerialIssuerMatch cert delta)) (REVOKED [] certificateHold)
                                      ,′e certStatusEq? (findStatus (JfindSerialIssuerMatch cert crl)) (REVOKED [] certificateHold) of λ where
                                      (yes g₁ , _) →
                                        case everifiyMask? reasonsMask temp₁ of λ where
                                          (yes p₃) → ((REVOKED (unonRevocationReason reasonsMask temp₁) certificateHold)) ,
                                                     fromUnrevokedToRevoked₂ (there (there (there (there (there (there (here refl))))))) s₁ refl refl p p₁ p₅ p₂ p₄ g₁ (p₃ , refl)
                                          (no ¬p₃) → UNREVOKED (unonRevocationReason reasonsMask temp₁) ,
                                                     fromUnrevokedToUnrevoked₄₂ s₁ refl refl p₁ p₅ ¬p₃ refl
                                      (no ¬g₁ , yes g₂) →
                                        case everifiyMask? reasonsMask temp of λ where
                                          (yes p₃) → ((REVOKED (unonRevocationReason reasonsMask temp) certificateHold)) ,
                                                     fromUnrevokedToRevoked₃ (there (there (there (there (there (there (here refl))))))) s₁ refl refl p p₁ p₅ p₂ p₄ ¬g₁ g₂ (p₃ , refl)
                                          (no ¬p₃) → UNREVOKED (unonRevocationReason reasonsMask temp) ,
                                                     fromUnrevokedToUnrevoked₄₃ s₁ refl refl p₁ p₅ ¬p₃ refl
                                      (no ¬g₁ , no ¬g₂) → 
                                        case certStatusEq? (findStatus (JfindSerialIssuerMatch cert delta)) (REVOKED [] removeFromCRL)
                                          ,′e certStatusEq? (findStatus (JfindSerialIssuerMatch cert crl)) (REVOKED [] removeFromCRL) of λ where
                                          (yes h₁ , _) →
                                            case everifiyMask? reasonsMask temp₁ of λ where
                                              (yes p₃) → UNREVOKED (unonRevocationReason reasonsMask temp₁) ,
                                                         fromUnrevokedToUnrevoked₁₂ s₁ refl refl p p₁ p₅ p₂ p₄ h₁ (p₃ , refl)
                                              (no ¬p₃) → UNREVOKED (unonRevocationReason reasonsMask temp₁) ,
                                                         fromUnrevokedToUnrevoked₄₂ s₁ refl refl p₁ p₅ ¬p₃ refl
                                          (no ¬h₁ , yes h₂) →
                                            case everifiyMask? reasonsMask temp of λ where
                                              (yes p₃) → UNREVOKED (unonRevocationReason reasonsMask temp) ,
                                                         fromUnrevokedToUnrevoked₁₃ s₁ refl refl p p₁ p₅ p₂ p₄ ¬h₁ h₂ (p₃ , refl)
                                              (no ¬p₃) → UNREVOKED (unonRevocationReason reasonsMask temp) ,
                                                         fromUnrevokedToUnrevoked₄₃ s₁ refl refl p₁ p₅ ¬p₃ refl
                                          (no ¬h₁ , no ¬h₂) → 
                                            case certStatusEq? (findStatus (JfindSerialIssuerMatch cert delta)) (REVOKED [] privilegeWithdrawn)
                                              ,′e certStatusEq? (findStatus (JfindSerialIssuerMatch cert crl)) (REVOKED [] privilegeWithdrawn) of λ where
                                              (yes i₁ , _) →
                                                case everifiyMask? reasonsMask temp₁ of λ where
                                                  (yes p₃) → ((REVOKED (unonRevocationReason reasonsMask temp₁) privilegeWithdrawn)) ,
                                                             fromUnrevokedToRevoked₂ (there (there (there (there (there (there (there (here refl)))))))) s₁ refl refl p p₁ p₅ p₂ p₄ i₁ (p₃ , refl)
                                                  (no ¬p₃) → UNREVOKED (unonRevocationReason reasonsMask temp₁) ,
                                                             fromUnrevokedToUnrevoked₄₂ s₁ refl refl p₁ p₅ ¬p₃ refl
                                              (no ¬i₁ , yes i₂) →
                                                case everifiyMask? reasonsMask temp of λ where
                                                  (yes p₃) → ((REVOKED (unonRevocationReason reasonsMask temp) privilegeWithdrawn)) ,
                                                             fromUnrevokedToRevoked₃ (there (there (there (there (there (there (there (here refl)))))))) s₁ refl refl p p₁ p₅ p₂ p₄ ¬i₁ i₂ (p₃ , refl)
                                                  (no ¬p₃) → UNREVOKED (unonRevocationReason reasonsMask temp) ,
                                                             fromUnrevokedToUnrevoked₄₃ s₁ refl refl p₁ p₅ ¬p₃ refl
                                              (no ¬i₁ , no ¬i₂) → 
                                                case certStatusEq? (findStatus (JfindSerialIssuerMatch cert delta)) (REVOKED [] aACompromise)
                                                  ,′e certStatusEq? (findStatus (JfindSerialIssuerMatch cert crl)) (REVOKED [] aACompromise) of λ where
                                                  (yes j₁ , _) →
                                                    case everifiyMask? reasonsMask temp₁ of λ where
                                                      (yes p₃) → ((REVOKED (unonRevocationReason reasonsMask temp₁) aACompromise)) ,
                                                                 fromUnrevokedToRevoked₂ (there (there (there (there (there (there (there (there (here refl))))))))) s₁ refl refl p p₁ p₅ p₂ p₄ j₁ (p₃ , refl)
                                                      (no ¬p₃) → UNREVOKED (unonRevocationReason reasonsMask temp₁) ,
                                                                 fromUnrevokedToUnrevoked₄₂ s₁ refl refl p₁ p₅ ¬p₃ refl
                                                  (no ¬j₁ , yes j₂) →
                                                    case everifiyMask? reasonsMask temp of λ where
                                                      (yes p₃) → ((REVOKED (unonRevocationReason reasonsMask temp) aACompromise)) ,
                                                                 fromUnrevokedToRevoked₃ (there (there (there (there (there (there (there (there (here refl))))))))) s₁ refl refl p p₁ p₅ p₂ p₄ ¬j₁ j₂ (p₃ , refl)
                                                      (no ¬p₃) → UNREVOKED (unonRevocationReason reasonsMask temp) ,
                                                                 fromUnrevokedToUnrevoked₄₃ s₁ refl refl p₁ p₅ ¬p₃ refl
                                                  (no ¬j₁ , no ¬j₂) → 
                                                    case certStatusEq? (findStatus (JfindSerialIssuerMatch cert delta)) (REVOKED [] allReasons)
                                                      ,′e certStatusEq? (findStatus (JfindSerialIssuerMatch cert crl)) (REVOKED [] allReasons) of λ where
                                                      (yes k₁ , _) →
                                                        case everifiyMask? reasonsMask temp₁ of λ where
                                                          (yes p₃) → ((REVOKED (unonRevocationReason reasonsMask temp₁) allReasons)) ,
                                                                     fromUnrevokedToRevoked₂ (there (there (there (there (there (there (there (there (there (here refl)))))))))) s₁ refl refl p p₁ p₅ p₂ p₄ k₁ (p₃ , refl)
                                                          (no ¬p₃) → UNREVOKED (unonRevocationReason reasonsMask temp₁) ,
                                                                     fromUnrevokedToUnrevoked₄₂ s₁ refl refl p₁ p₅ ¬p₃ refl
                                                      (no ¬k₁ , yes k₂) →
                                                        case everifiyMask? reasonsMask temp of λ where
                                                          (yes p₃) → ((REVOKED (unonRevocationReason reasonsMask temp) allReasons)) ,
                                                                     fromUnrevokedToRevoked₃ (there (there (there (there (there (there (there (there (there (here refl)))))))))) s₁ refl refl p p₁ p₅ p₂ p₄ ¬k₁ k₂ (p₃ , refl)
                                                          (no ¬p₃) → UNREVOKED (unonRevocationReason reasonsMask temp) ,
                                                                     fromUnrevokedToUnrevoked₄₃ s₁ refl refl p₁ p₅ ¬p₃ refl
                                                      (no ¬k₁ , no ¬k₂) → UNREVOKED (unonRevocationReason reasonsMask temp) ,
                                                                          fromUnrevokedToUnrevoked₅ s₁ refl refl ¬k₁ ¬k₂ refl
          (yes p₂ , no ¬p₄) → UNREVOKED reasonsMask ,
                              fromUnrevokedToUnrevoked₃ s₁ refl refl p₁ p₅ ¬p₄ refl
          (no ¬p₂ , _) → UNREVOKED reasonsMask ,
                         fromUnrevokedToUnrevoked₂ s₁ refl p p₁ ¬p₂ refl
    (yes p , yes p₁ , no ¬p₅) → UNREVOKED reasonsMask ,
                                fromUnrevokedToUnrevoked₉ s₁ refl refl ¬p₅ refl
    (yes p , no ¬p₁ , _) → UNREVOKED reasonsMask ,
                           fromUnrevokedToUnrevoked₈ s₁ refl ¬p₁ refl
    (no ¬p , _ , _) → UNREVOKED reasonsMask ,
                      fromUnrevokedToUnrevoked₇ s₁ refl ¬p refl
validStateTransition (mkRevInputs cert crl nothing) dp s₁@(UNREVOKED reasonsMask) =
  let
    temp = (DcomputeIntReasonMask dp crl)
  in
  case (_≟_ (Dp∈Cert cert dp) true) ,′e (_≟_ (isDeltaCRL crl) false) of λ where
    (yes p , yes p₁) →
      case (bscopeCompleteCRL? cert dp p crl p₁) ,′e (everifiyMask? reasonsMask temp)  of λ where
          (yes p₂ , yes p₃) →
            case certStatusEq? (findStatus (JfindSerialIssuerMatch cert crl)) (REVOKED [] unspecified) of λ where
              (yes a) → REVOKED (unonRevocationReason reasonsMask temp) unspecified ,
                        fromUnrevokedToRevoked₁ (here refl) s₁ refl p p₁ p₂ a (p₃ , refl)
              (no _) →
                case certStatusEq? (findStatus (JfindSerialIssuerMatch cert crl)) (REVOKED [] keyCompromise) of λ where
                (yes b) → REVOKED (unonRevocationReason reasonsMask temp) keyCompromise ,
                          fromUnrevokedToRevoked₁ (there (here refl)) s₁ refl p p₁ p₂ b (p₃ , refl)
                (no _) →
                  case certStatusEq? (findStatus (JfindSerialIssuerMatch cert crl)) (REVOKED [] cACompromise) of λ where
                    (yes c) → REVOKED (unonRevocationReason reasonsMask temp) cACompromise ,
                              fromUnrevokedToRevoked₁ (there (there (here refl))) s₁ refl p p₁ p₂ c (p₃ , refl)
                    (no _) →
                      case certStatusEq? (findStatus (JfindSerialIssuerMatch cert crl)) (REVOKED [] affiliationChanged) of λ where
                        (yes d) → REVOKED (unonRevocationReason reasonsMask temp) affiliationChanged ,
                                  fromUnrevokedToRevoked₁ (there (there (there (here refl)))) s₁ refl p p₁ p₂ d (p₃ , refl)
                        (no _) →
                          case certStatusEq? (findStatus (JfindSerialIssuerMatch cert crl)) (REVOKED [] superseded) of λ where
                            (yes e) → REVOKED (unonRevocationReason reasonsMask temp) superseded ,
                                      fromUnrevokedToRevoked₁ (there (there (there (there (here refl))))) s₁ refl p p₁ p₂ e (p₃ , refl)
                            (no _) →
                              case certStatusEq? (findStatus (JfindSerialIssuerMatch cert crl)) (REVOKED [] cessationOfOperation) of λ where
                                (yes f) → REVOKED (unonRevocationReason reasonsMask temp) cessationOfOperation ,
                                          fromUnrevokedToRevoked₁ (there (there (there (there (there (here refl)))))) s₁ refl p p₁ p₂ f (p₃ , refl)
                                (no _) →
                                  case certStatusEq? (findStatus (JfindSerialIssuerMatch cert crl)) (REVOKED [] certificateHold) of λ where
                                    (yes g) → REVOKED (unonRevocationReason reasonsMask temp) certificateHold ,
                                              fromUnrevokedToRevoked₁ (there (there (there (there (there (there (here refl))))))) s₁ refl p p₁ p₂ g (p₃ , refl)
                                    (no _) →
                                      case certStatusEq? (findStatus (JfindSerialIssuerMatch cert crl)) (REVOKED [] privilegeWithdrawn) of λ where
                                        (yes h) → REVOKED (unonRevocationReason reasonsMask temp) privilegeWithdrawn ,
                                                  fromUnrevokedToRevoked₁ (there (there (there (there (there (there (there (here refl)))))))) s₁ refl p p₁ p₂ h (p₃ , refl)
                                        (no _) →
                                          case certStatusEq? (findStatus (JfindSerialIssuerMatch cert crl)) (REVOKED [] aACompromise) of λ where
                                            (yes i) → REVOKED (unonRevocationReason reasonsMask temp) aACompromise ,
                                                      fromUnrevokedToRevoked₁ (there (there (there (there (there (there (there (there (here refl))))))))) s₁ refl p p₁ p₂ i (p₃ , refl)
                                            (no _) →
                                              case certStatusEq? (findStatus (JfindSerialIssuerMatch cert crl)) (REVOKED [] allReasons) of λ where
                                                (yes j) → REVOKED (unonRevocationReason reasonsMask temp) allReasons ,
                                                          fromUnrevokedToRevoked₁ (there (there (there (there (there (there (there (there (there (here refl)))))))))) s₁ refl p p₁ p₂ j (p₃ , refl)
                                                (no ¬j) →
                                                  case certStatusEq? (findStatus (JfindSerialIssuerMatch cert crl)) (REVOKED [] removeFromCRL) of λ where
                                                    (yes k) → UNREVOKED (unonRevocationReason reasonsMask temp) ,
                                                              fromUnrevokedToUnrevoked₁₁ s₁ refl p p₁ p₂ k (p₃ , refl)
                                                    (no ¬k) → UNREVOKED (unonRevocationReason reasonsMask temp) ,
                                                              fromUnrevokedToUnrevoked₆ s₁ refl ¬k refl
          (yes p₂ , no ¬p₃) → UNREVOKED (unonRevocationReason reasonsMask temp) ,
                              fromUnrevokedToUnrevoked₄₁ s₁ refl p₁ ¬p₃ refl
          (no ¬p₂ , _) → UNREVOKED reasonsMask ,
                         fromUnrevokedToUnrevoked₂ s₁ refl p p₁ ¬p₂ refl 
    (yes p , no ¬p₁) → UNREVOKED reasonsMask ,
                       fromUnrevokedToUnrevoked₈ s₁ refl ¬p₁ refl
    (no ¬p , _) → UNREVOKED reasonsMask ,
                  fromUnrevokedToUnrevoked₇ s₁ refl ¬p refl

data CoreRevocationCheck (ri : RevInputs) : List (Exists─ _ DistPoint) → ValidRevocationState → ValidRevocationState → Set where
  zeroStep : ∀{s} → CoreRevocationCheck ri [] s s
  oneStep : ∀ {@0 bs} (dp : DistPoint bs) (dps : List (Exists─ _ DistPoint)) (vrs₁ vrs₂ vrs₃ : ValidRevocationState)
            → ValidStateTransition ri dp vrs₁ vrs₂
            → CoreRevocationCheck ri dps vrs₂ vrs₃ 
            → CoreRevocationCheck ri ((-, dp) ∷ dps) vrs₁ vrs₃

coreRevocationCheck : (ri : RevInputs) → (dps : List (Exists─ _ DistPoint)) → (vrs₁ : ValidRevocationState) → Σ[ vrs₂ ∈ ValidRevocationState ] CoreRevocationCheck ri dps vrs₁ vrs₂
coreRevocationCheck ri [] vrs₁ = vrs₁ , zeroStep
coreRevocationCheck ri ((fst , dp) ∷ rest) vrs₁ = proj₁ rest,pf , foo
  where
  vrs₂,pf : Σ[ vrs₂ ∈ ValidRevocationState ] ValidStateTransition ri dp vrs₁ vrs₂
  vrs₂,pf = validStateTransition ri dp vrs₁

  rest,pf : Σ[ vrs₃ ∈ ValidRevocationState ] CoreRevocationCheck ri rest (proj₁ vrs₂,pf) vrs₃
  rest,pf = coreRevocationCheck ri rest (proj₁ vrs₂,pf)

  foo = oneStep dp rest vrs₁ (proj₁ vrs₂,pf) (proj₁ rest,pf) (proj₂ vrs₂,pf) (proj₂ rest,pf)

data VerifiedCertStateCRL (ri : RevInputs) : State → State → Set where
  r₁₁  : ∀ {@0 bs} (dps : SequenceOf DistPoint bs)
                    → ¬ (Dps∈Cert (RevInputs.cert ri) dps ≡ true)
                    → VerifiedCertStateCRL ri initState undeterminedState

  r₁₂  : VerifiedCertStateCRL ri initState undeterminedState -- unguarded??
  
  r₂  : ∀ {@0 bs} (dps : SequenceOf DistPoint bs) (pf : Σ[ s ∈ ValidRevocationState ] CoreRevocationCheck ri (IList.toList _ dps) initValidRevocationState s)
                    → Dps∈Cert (RevInputs.cert ri) dps ≡ true
                    → isRevoked (proj₁ pf) ≡ true
                    → VerifiedCertStateCRL ri initState (validState (proj₁ pf))
                    
  r₃  : ∀ {@0 bs} (dps : SequenceOf DistPoint bs) (pf : Σ[ s ∈ ValidRevocationState ] CoreRevocationCheck ri (IList.toList _ dps) initValidRevocationState s)
                    → Dps∈Cert (RevInputs.cert ri) dps ≡ true
                    → ¬ (isRevoked (proj₁ pf) ≡ true)
                    → findInStateRm allReasons (proj₁ pf) ≡ true
                    → VerifiedCertStateCRL ri initState (validState (proj₁ pf))

  r₄  : ∀ {@0 bs} (dps : SequenceOf DistPoint bs) (pf : Σ[ s ∈ ValidRevocationState ] CoreRevocationCheck ri (IList.toList _ dps) initValidRevocationState s)
                    → Dps∈Cert (RevInputs.cert ri) dps ≡ true
                    → ¬ (isRevoked (proj₁ pf) ≡ true)
                    → ¬ (findInStateRm allReasons (proj₁ pf) ≡ true)
                    → VerifiedCertStateCRL ri initState undeterminedState

  r₅ : ∀{s rm rsn} → (s ≡ validState (REVOKED rm rsn)) → VerifiedCertStateCRL ri s undeterminedState

  r₆ : ∀{s} → (s ≡ undeterminedState) → VerifiedCertStateCRL ri s undeterminedState

  r₇ : ∀{s rm rest} → (s ≡ validState (UNREVOKED (rm ∷ rest))) → VerifiedCertStateCRL ri s undeterminedState

verifiedCertStateCRL : (ri : RevInputs) → (s₁ : State) → Σ[ s₂ ∈ State ] VerifiedCertStateCRL ri s₁ s₂
verifiedCertStateCRL (mkRevInputs cert crl delta) s@(validState (REVOKED reasonMask reason)) = undeterminedState , r₅ refl
verifiedCertStateCRL ri@(mkRevInputs cert crl delta) s₁@(validState (UNREVOKED [])) =
  case Cert.getCRLDIST cert of λ where
    (─ .[] , none) → undeterminedState , r₁₂
    (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mk×ₚ dps sndₚ₁) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) →
      case _≟_ (Dps∈Cert cert dps) true  of λ where
        (yes p) →
          case coreRevocationCheck ri (IList.toList _ dps) initValidRevocationState of λ where
            v →
              case _≟_ (isRevoked (proj₁ v)) true of λ where
                (yes p₁) → (validState (proj₁ v)) , (r₂ dps v p p₁)
                (no ¬p₁) →
                  case _≟_ (findInStateRm allReasons (proj₁ v)) true of λ where
                    (yes p₂) → (validState (proj₁ v)) , (r₃ dps v p ¬p₁ p₂)
                    (no ¬p₂) → undeterminedState , (r₄ dps v p ¬p₁ ¬p₂)
        (no ¬p) → undeterminedState , r₁₁ dps ¬p
verifiedCertStateCRL (mkRevInputs cert crl delta) s@(validState (UNREVOKED (rm ∷ rest))) = undeterminedState , r₇ refl
verifiedCertStateCRL (mkRevInputs cert crl delta) undeterminedState = undeterminedState , r₆ refl

data VerifiedCertStateCRLs {@0 bs} (cert : Cert bs) : List (Exists─ _ CRL.CertList) → State → (Exists─ _ CRL.CertList) → State → Set where            
  r₁  : ∀ {@0 bs} (crl : CRL.CertList bs) (s₁ s₂ : State)
            → VerifiedCertStateCRL (mkRevInputs{_}{_}{[]} cert crl nothing) s₁ s₂ 
            → VerifiedCertStateCRLs cert [ (-, crl) ] s₁ (-, crl) s₂
  
  r₂  : ∀ {@0 bs} (crl : CRL.CertList bs) (crls : List (Exists─ _ CRL.CertList)) (s₁ s₂ : State)
            → VerifiedCertStateCRL (mkRevInputs{_}{_}{[]} cert crl nothing) s₁ s₂
            → isValidState s₂ ≡ true
            → VerifiedCertStateCRLs cert ((-, crl) ∷ crls) s₁ (-, crl) s₂

  r₃  : ∀ {@0 bs₁ bs₂} (crl : CRL.CertList bs₁) (crls : List (Exists─ _ CRL.CertList)) (s₁ s₂ s₃ : State)
            → VerifiedCertStateCRL (mkRevInputs{_}{_}{[]} cert crl nothing) s₁ s₂
            → ¬ (isValidState s₂ ≡ true)
            → (crl₂ : CRL.CertList bs₂)
            → VerifiedCertStateCRLs cert crls s₁ (-, crl₂) s₃
            → isValidState s₃ ≡ true
            → VerifiedCertStateCRLs cert ((-, crl) ∷ crls) s₁ (-, crl₂) s₃

  r₄  : ∀ {@0 bs₁ bs₂} (crl : CRL.CertList bs₁) (crls : List (Exists─ _ CRL.CertList)) (s₁ s₂ s₃ : State)
            → VerifiedCertStateCRL (mkRevInputs{_}{_}{[]} cert crl nothing) s₁ s₂
            → ¬ (isValidState s₂ ≡ true)
            → (crl₂ : CRL.CertList bs₂)
            → VerifiedCertStateCRLs cert crls s₁ (-, crl₂) s₃
            → ¬ (isValidState s₃ ≡ true)
            → VerifiedCertStateCRLs cert ((-, crl) ∷ crls) s₁ (-, crl₂) s₃

verifiedCertStateCRLs : ∀ {@0 bs} → (cert : Cert bs) → (x : Exists─ _ CRL.CertList) → (x₁ : List (Exists─ _ CRL.CertList))
                                  → (s₁ : State) → Σ[ crl ∈ (Exists─ _ CRL.CertList) ] (Σ[ s₂ ∈ State ] VerifiedCertStateCRLs cert (x ∷ x₁) s₁ crl s₂)
verifiedCertStateCRLs cert (fst , crl) [] s₁ =
  case verifiedCertStateCRL (mkRevInputs{_}{_}{[]} cert crl nothing) s₁ of λ where
     v → (-, crl) , ((proj₁ v) , r₁ crl s₁ (proj₁ v) (proj₂ v))
verifiedCertStateCRLs cert (fst , crl) rest@(x ∷ x₁) s₁ =
   case verifiedCertStateCRL (mkRevInputs{_}{_}{[]} cert crl nothing) s₁ of λ where
     v →
       case _≟_ (isValidState (proj₁ v)) true of λ where
          (yes p) → (-, crl) , ((proj₁ v) , (r₂ crl rest s₁ (proj₁ v) (proj₂ v) p))
          (no ¬p) →
            case verifiedCertStateCRLs cert x x₁ s₁ of λ where
              (crl₂ , vv) →
                case _≟_ (isValidState (proj₁ vv)) true of λ where
                  (yes pp) → crl₂ , ((proj₁ vv) , r₃ crl rest s₁ (proj₁ v) (proj₁ vv) (proj₂ v) ¬p (proj₂ crl₂) (proj₂ vv) pp)
                  (no ¬pp) → crl₂ , ((proj₁ vv) , r₄ crl rest s₁ (proj₁ v) (proj₁ vv) (proj₂ v) ¬p (proj₂ crl₂) (proj₂ vv) ¬pp)

data VerifiedChainStateCRLs (crls : List (Exists─ _ CRL.CertList)) : List (Exists─ _ Cert) → State → List (Exists─ _ CRL.CertList) → List State → Set where
  r₁  : (cert : Exists─ _ Cert) (crl : Exists─ _ CRL.CertList) (s₁ s₂ : State)
            → VerifiedCertStateCRLs (proj₂ cert) crls s₁ crl s₂
            → VerifiedChainStateCRLs crls [ cert ] s₁ [ crl ] [ s₂ ]
  
  r₂  : (cert : Exists─ _ Cert) (certs : List (Exists─ _ Cert)) (crl : Exists─ _ CRL.CertList) (s₁ s₂ : State) (s₃ : List State)
            → VerifiedCertStateCRLs (proj₂ cert) crls s₁ crl s₂
            → (restCrls : List (Exists─ _ CRL.CertList))
            → VerifiedChainStateCRLs crls certs s₁ restCrls s₃
            → VerifiedChainStateCRLs crls (cert ∷ certs) s₁ (crl ∷ restCrls) (s₂ ∷ s₃)


verifiedChainStateCRLs : (crl : Exists─ _ CRL.CertList) → (crls : List (Exists─ _ CRL.CertList)) → (cert : Exists─ _ Cert) → (certs : List (Exists─ _ Cert)) → (s₁ : State)
                               → Σ[ crlFiltered ∈ List (Exists─ _ CRL.CertList) ] (Σ[ s₂ ∈ List State ] VerifiedChainStateCRLs (crl ∷ crls) (cert ∷ certs) s₁ crlFiltered s₂)
verifiedChainStateCRLs crl crls (fst , cert) [] s₁ =
  case verifiedCertStateCRLs cert crl crls s₁ of λ where
    (crll , s₂ , pf) → [ crll ] , ([ s₂ ] , r₁ (-, cert) crll s₁ s₂ pf)
verifiedChainStateCRLs crl crls (fst , cert) rest@(x ∷ x₁) s₁ =
  ((proj₁ s₂,pf) ∷ (proj₁ rest,pf)) ,
    ((proj₁ (proj₂ s₂,pf)) ∷ (proj₁ (proj₂ rest,pf))) ,
      r₂ (-, cert) rest (proj₁ s₂,pf) s₁ (proj₁ (proj₂ s₂,pf)) (proj₁ (proj₂ rest,pf)) (proj₂ (proj₂ s₂,pf)) (proj₁ rest,pf) (proj₂ (proj₂ rest,pf))
  where
  s₂,pf : Σ[ crll ∈ Exists─ _ CRL.CertList ] (Σ[ s₂ ∈ State ] VerifiedCertStateCRLs cert (crl ∷ crls) s₁ crll s₂)
  s₂,pf = verifiedCertStateCRLs cert crl crls s₁

  rest,pf : Σ[ crll ∈ List (Exists─ _ CRL.CertList) ] (Σ[ s₃ ∈ List State ] VerifiedChainStateCRLs (crl ∷ crls) rest s₁ crll s₃)
  rest,pf = verifiedChainStateCRLs crl crls x x₁ s₁
