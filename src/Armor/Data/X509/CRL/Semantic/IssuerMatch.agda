{-# OPTIONS --sized-types #-}

open import Armor.Binary
open import Armor.Data.X509
open import Armor.Data.X509.CRL.CertList.TCB as CRL
open import Armor.Data.X509.CRL.Extension.TCB as CRLExtension
open import Armor.Data.X509.Semantic.Chain.NameMatch
open import Armor.Data.X509.CRL.Extension.IDP.TCB
open import Armor.Data.X509.Extension.CRLDistPoint.DistPoint.Name.TCB
-- import      Armor.Data.X509.Extension.TCB.OIDs as OIDs
-- open import Armor.Data.X509.Semantic.Cert.Utils
open import Armor.Data.X509.Extension.CRLDistPoint.DistPoint.TCB
open import Armor.Data.X509.GeneralNames.GeneralName.TCB
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
open import Armor.Grammar.IList as IList
import      Armor.Grammar.Parallel.TCB
open import Armor.Prelude

module Armor.Data.X509.CRL.Semantic.IssuerMatch where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8
open Armor.Grammar.Parallel.TCB UInt8



-- -- -- R1 : ∀ {@0 bs} → Cert bs → Set
-- -- -- R1 c = _≋_{A = SignAlg} (Cert.getTBSCertSignAlg c) (Cert.getCertSignAlg c)

-- -- -- r1 : ∀ {@0 bs} (c : Cert bs) → Dec (R1 c)
-- -- -- r1 c = Cert.getTBSCertSignAlg c ≋? Cert.getCertSignAlg c




--  -- For each distribution point (DP) in the certificate's CRL
--  --   distribution points extension, for each corresponding CRL in the
--  --   local CRL cache

-- VerifyIssuerCompleteCRLScope : ∀ {@0 bs₁ bs₂} → Cert bs₁ → CRL.CertList bs₂ → Set
-- VerifyIssuerCompleteCRLScope cert crl = case (Cert.getCRLDIST cert) of λ
--   where
--   (_ , none) → ⊥
--   (_ , some (mkExtensionFields _ _ _ (mkTLV _ (mkTLV _ (mk×ₚ fstₚ₁ sndₚ₁) _ _) _ _) _)) → B1 fstₚ₁ × B22 × B23 × B24
--     where
--     helper₁ : ∀ {@0 bs} → SequenceOf GeneralName bs → Set
--     helper₁ nil = ⊥
--     helper₁ (cons (mkIListCons (dirname (mkTLV len issr len≡ bs≡₁)) tail₁ bs≡)) = NameMatch issr (CRL.CertList.getIssuer crl) ⊎ helper₁ tail₁
--     helper₁ (cons (mkIListCons _ tail₁ bs≡)) = helper₁ tail₁

--     helper₂ : Set
--     helper₂ = case CRL.CertList.getIDP crl of λ where
--       (_ , none) → ⊥
--       (_ , some (mkExtensionFields _ _ _ (mkTLV _ (mkTLV _ (mkIDPFieldsSeqFields _ _ _ _ (mkDefault none notDefault) _ _ _) _ _) _ _) _)) → ⊥
--       (_ , some (mkExtensionFields _ _ _ (mkTLV _ (mkTLV _ (mkIDPFieldsSeqFields _ _ _ _
--         (mkDefault (some (mkTLV _ (mkBoolValue false _ _ _) _ _)) notDefault) _ _ _) _ _) _ _) _)) → ⊥
--       (_ , some (mkExtensionFields _ _ _ (mkTLV _ (mkTLV _ (mkIDPFieldsSeqFields _ _ _ _
--         (mkDefault (some (mkTLV _ (mkBoolValue true _ _ _) _ _)) notDefault) _ _ _) _ _) _ _) _)) → ⊤

--     helper₃ : ∀ {@0 bs} → DistPoint bs → Set
--     helper₃ (mkTLV len (mkDistPointFields crldp crldprsn none notOnlyReasonT bs≡₁) len≡ bs≡) = NameMatch (Cert.getIssuer cert) (CRL.CertList.getIssuer crl)
--     helper₃ (mkTLV len (mkDistPointFields crldp crldprsn (some (mkTLV len₁ (mk×ₚ fstₚ₁ sndₚ₁) len≡₁ bs≡₂)) notOnlyReasonT bs≡₁) len≡ bs≡) = helper₁ fstₚ₁ × helper₂

--     -- If the DP includes cRLIssuer, then verify that the issuer
--     -- field in the complete CRL matches cRLIssuer in the DP and
--     -- that the complete CRL contains an issuing distribution
--     -- point extension with the indirectCRL boolean asserted.
--     -- Otherwise, verify that the CRL issuer matches the
--     -- certificate issuer.
--     B1 : ∀ {@0 bs} → SequenceOf DistPoint bs → Set
--     B1 nil = ⊥
--     B1 (cons (mkIListCons dp rest bs≡)) = helper₃ dp ⊎ B1 rest

--     -- If the onlyContainsUserCerts boolean is asserted in
--     --               the IDP CRL extension, verify that the certificate
--     --               does not include the basic constraints extension with
--     --               the cA boolean asserted.
--     B22 : Set
--     B22 = case CRL.CertList.getIDP crl of λ where
--       (_ , none) → ⊤
--       (_ , some (mkExtensionFields _ _ _ (mkTLV _ (mkTLV _ (mkIDPFieldsSeqFields _  (mkDefault none notDefault) _ _ _ _ _ _) _ _) _ _) _)) → ⊤
--       (_ , some (mkExtensionFields _ _ _ (mkTLV _ (mkTLV _ (mkIDPFieldsSeqFields _ 
--         (mkDefault (some (mkTLV _ (mkBoolValue false _ _ _) _ _)) notDefault) _ _ _ _ _ _) _ _) _ _) _)) → ⊤
--       (_ , some (mkExtensionFields _ _ _ (mkTLV _ (mkTLV _ (mkIDPFieldsSeqFields _
--         (mkDefault (some (mkTLV _ (mkBoolValue true _ _ _) _ _)) notDefault) _ _ _ _ _ _) _ _) _ _) _)) →
--           case Cert.isCA cert of λ where
--             (just true) → ⊥
--             (just false) → ⊤
--             nothing → ⊤


--     -- If the onlyContainsCACerts boolean is asserted in the
--                   -- IDP CRL extension, verify that the certificate
--                   -- includes the basic constraints extension with the cA
--                   -- boolean asserted.
--     B23 : Set
--     B23 = case CRL.CertList.getIDP crl of λ where
--       (_ , none) → ⊤
--       (_ , some (mkExtensionFields _ _ _ (mkTLV _ (mkTLV _ (mkIDPFieldsSeqFields _ _ (mkDefault none notDefault) _ _ _ _ _) _ _) _ _) _)) → ⊤
--       (_ , some (mkExtensionFields _ _ _ (mkTLV _ (mkTLV _ (mkIDPFieldsSeqFields _ _
--         (mkDefault (some (mkTLV _ (mkBoolValue false _ _ _) _ _)) notDefault) _ _ _ _ _) _ _) _ _) _)) → ⊤
--       (_ , some (mkExtensionFields _ _ _ (mkTLV _ (mkTLV _ (mkIDPFieldsSeqFields _ _
--         (mkDefault (some (mkTLV _ (mkBoolValue true _ _ _) _ _)) notDefault) _ _ _ _ _) _ _) _ _) _)) →
--           case Cert.isCA cert of λ where
--             (just true) → ⊤
--             (just false) → ⊥
--             nothing → ⊥


--     -- Verify that the onlyContainsAttributeCerts boolean is
--     --             not asserted.
--     B24 : Set
--     B24 = case CRL.CertList.getIDP crl of λ where
--       (_ , none) → ⊤
--       (_ , some (mkExtensionFields _ _ _ (mkTLV _ (mkTLV _ (mkIDPFieldsSeqFields _ _ _ _ _ (mkDefault none notDefault) _ _) _ _) _ _) _)) → ⊤
--       (_ , some (mkExtensionFields _ _ _ (mkTLV _ (mkTLV _ (mkIDPFieldsSeqFields _ _ _ _ _
--         (mkDefault (some (mkTLV _ (mkBoolValue false _ _ _) _ _)) notDefault) _ _) _ _) _ _) _)) → ⊤
--       (_ , some (mkExtensionFields _ _ _ (mkTLV _ (mkTLV _ (mkIDPFieldsSeqFields _ _ _ _ _
--         (mkDefault (some (mkTLV _ (mkBoolValue true _ _ _) _ _)) notDefault) _ _) _ _) _ _) _)) → ⊥
      




--     -- If the distribution point name is present in the IDP
--                   -- CRL extension and the distribution field is present in
--                   -- the DP, then verify that one of the names in the IDP
--                   -- matches one of the names in the DP.  If the
--                   -- distribution point name is present in the IDP CRL
--                   -- extension and the distribution field is omitted from
--                   -- the DP, then verify that one of the names in the IDP
--                   -- matches one of the names in the cRLIssuer field of the
--                   -- DP.

--     -- helper₄ : ∀ {@0 bs} → DistPoint bs → Set
--     -- helper₄ dp = case CRL.CertList.getIDP crl of λ where
--     --   (_ , none) → ⊥
--     --   (_ , some (mkExtensionFields _ _ _ (mkTLV _ (mkTLV _ (mkIDPFieldsSeqFields none _ _ _ _ _ _ _) _ _) _ _) _)) → {!!}
--     --   (_ , some (mkExtensionFields _ _ _ (mkTLV _ (mkTLV _ (mkIDPFieldsSeqFields (some (mkTLV _ (fullname x) len≡ bs≡)) _ _ _ _ _ _ _) _ _) _ _) _)) → {!!}
--     --   (_ , some (mkExtensionFields _ _ _ (mkTLV _ (mkTLV _ (mkIDPFieldsSeqFields (some (mkTLV _ (nameRTCrlissr x) len≡ bs≡)) _ _ _ _ _ _ _) _ _) _ _) _)) → {!!}



-- Revocation reason enumeration
data RevocationReason : Set where
  keyCompromise       : RevocationReason
  cACompromise        : RevocationReason
  affiliationChanged  : RevocationReason
  superseded          : RevocationReason
  cessationOfOperation : RevocationReason
  certificateHold     : RevocationReason
  privilegeWithdrawn  : RevocationReason
  aACompromise        : RevocationReason
  allReasons          : RevocationReason

-- Set of reasons
ReasonsMask : Set
ReasonsMask = List RevocationReason

-- Certificate status
data CertStatus : Set where
  unspecified          : CertStatus
  keyCompromise        : CertStatus
  cACompromise         : CertStatus
  affiliationChanged   : CertStatus
  superseded           : CertStatus
  cessationOfOperation : CertStatus
  certificateHold      : CertStatus
  removeFromCRL        : CertStatus
  privilegeWithdrawn   : CertStatus
  aACompromise         : CertStatus
  UNREVOKED            : CertStatus
  UNDETERMINED         : CertStatus

-- State Variables
record State : Set where
  constructor mkState
  field
    reasonsMask          : List RevocationReason
    certStatus           : CertStatus
    interimReasonsMask   : List RevocationReason

-- Initial State
initState : State
initState = mkState [] UNREVOKED []

record RevInputs : Set where
  constructor mkRevInputs
  field
    @0 {c cr} : List UInt8
    cert : Cert c
    crl : CRL.CertList cr
    useDeltas   : Bool


findInList : RevocationReason → List RevocationReason → Bool
findInList x [] = false
findInList x (x₁ ∷ x₂) = {!!}


-- Function to process revocation state
processRevocation : RevInputs → State → State
processRevocation (mkRevInputs cert crl useDeltas) (mkState reasonsMask certStatus interimReasonsMask) =
  case findInList allReasons reasonsMask of λ where
    true → {!!}
    false → {!!}


-- processRevocation inputs state with reasonsMask state ≟ allReasons | certStatus state ≟ UNREVOKED
-- ... | yes _ | yes _ = state
-- ... | no _ | no _ =
--   let
--     -- Placeholder for CRL distribution points processing
--     processDistributionPoint : State → State
--     processDistributionPoint s =
--       let
--         verifyIssuerAndScope : State → State
--         verifyIssuerAndScope s =
--           -- (1) Verify issuer and scope of the complete CRL
--           s -- Placeholder for issuer and scope verification logic

--         verifyIDPExtension : State → State
--         verifyIDPExtension s =
--           -- (2) Check issuing distribution point (IDP) CRL extension
--           s -- Placeholder for IDP extension verification logic

--       in verifyIDPExtension (verifyIssuerAndScope s)

--   in processDistributionPoint state -- Extend state processing with distribution points
















































-- -- Check if a reason is in the mask
-- containsReason : RevocationReason → ReasonsMask → Set
-- containsReason reason mask = reason ∈ mask

-- -- Union of two reason masks
-- unionReasons : ReasonsMask → ReasonsMask → ReasonsMask
-- unionReasons = _++_


-- -- ∀ {@0 bs₁ bs₂} → Cert bs₁ → CRL.CertList bs₂ → Set

-- -- CRL Validation function
-- validateCRL : ∀{bs₁ bs₂} → Cert bs₁ → CRL.CertList bs₂ → (useDeltas : Bool) → ReasonsMask → CertStatus → CertStatus
-- validateCRL cert crl ud rm cs = {!!}


-- -- cert useDeltas reasonsMask certStatus with cert.cRLDistributionPoints
-- -- ... | nothing  = UNDETERMINED
-- -- ... | just dps = processDistributionPoints dps reasonsMask certStatus
