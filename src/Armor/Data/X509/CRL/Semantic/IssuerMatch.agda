{-# OPTIONS --sized-types #-}

open import Armor.Binary
open import Armor.Data.X509
open import Armor.Data.X509.CRL.CertList.TCB as CRL
open import Armor.Data.X509.CRL.Extension.TCB as CRLExtension
open import Armor.Data.X509.Semantic.Chain.NameMatch
open import Armor.Data.X509.CRL.Extension.IDP.TCB
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



-- R1 : ∀ {@0 bs} → Cert bs → Set
-- R1 c = _≋_{A = SignAlg} (Cert.getTBSCertSignAlg c) (Cert.getCertSignAlg c)

-- r1 : ∀ {@0 bs} (c : Cert bs) → Dec (R1 c)
-- r1 c = Cert.getTBSCertSignAlg c ≋? Cert.getCertSignAlg c


-- If the DP includes cRLIssuer, then verify that the issuer
--               field in the complete CRL matches cRLIssuer in the DP and
--               that the complete CRL contains an issuing distribution
--               point extension with the indirectCRL boolean asserted.
--               Otherwise, verify that the CRL issuer matches the
--               certificate issuer.

-- The cRLIssuer identifies the entity that signs and issues the CRL.
--    If present, the cRLIssuer MUST only contain the distinguished name
--    (DN) from the issuer field of the CRL to which the DistributionPoint
--    is pointing.  The encoding of the name in the cRLIssuer field MUST be
--    exactly the same as the encoding in issuer field of the CRL.

R1 : ∀ {@0 bs₁ bs₂} → Cert bs₁ → CRL.CertList bs₂ → Set
R1 c crl = case (Cert.getCRLDIST c) of λ
  where
    (_ , none) → ⊤
    (_ , some (mkExtensionFields extnId extnId≡ crit
      (mkTLV len (mkTLV len₁ (mk×ₚ fstₚ₁ sndₚ₁) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) → helper fstₚ₁
        where
        helper : ∀ {@0 bs} → SequenceOf DistPoint bs → Set
        helper nil = ⊤
        helper (cons (mkIListCons (mkTLV len (mkDistPointFields crldp crldprsn none notOnlyReasonT bs≡₂) len≡ bs≡₁) t bs≡)) = helper t
        helper (cons (mkIListCons (mkTLV len (mkDistPointFields crldp crldprsn
          (some (mkTLV len₁ (mk×ₚ fstₚ₂ sndₚ₂) len≡₁ bs≡₃)) notOnlyReasonT bs≡₂) len≡ bs≡₁) t bs≡)) = helper₂ fstₚ₂ × helper t
            where
            helper₃ : Set
            helper₃ = case CRL.CertList.getIDP crl of λ where
                (_ , none) → ⊥
                (_ , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkIDPFieldsSeqFields distributionPoint onlyContainsUserCerts onlyContainsCACerts onlySomeReasons (mkDefault none notDefault) onlyContainsAttributeCerts notEmptyProp bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) → ⊥
                (_ , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkIDPFieldsSeqFields distributionPoint onlyContainsUserCerts onlyContainsCACerts onlySomeReasons (mkDefault (some (mkTLV len₂ (mkBoolValue true b vᵣ bs≡₅) len≡₂ bs≡₄)) notDefault) onlyContainsAttributeCerts notEmptyProp bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) → ⊤
                (_ , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkIDPFieldsSeqFields distributionPoint onlyContainsUserCerts onlyContainsCACerts onlySomeReasons (mkDefault (some (mkTLV len₂ (mkBoolValue false b vᵣ bs≡₅) len≡₂ bs≡₄)) notDefault) onlyContainsAttributeCerts notEmptyProp bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) → ⊥

            helper₂ : ∀ {@0 bs} → SequenceOf GeneralName bs → Set
            helper₂ nil = ⊤
            helper₂ (cons (mkIListCons (dirname (mkTLV len issr len≡ bs≡₁)) tail₁ bs≡)) = ((NameMatch issr (CRL.CertList.getIssuer crl)) × helper₃) × (helper₂ tail₁)
            helper₂ (cons (mkIListCons _ tail₁ bs≡)) = helper₂ tail₁




---- verify CRL issuer matches certificate issuer


---- verify CRL contains an issuing distribution point extension with the indirectCRL boolean asserted
helper₃ : ∀ {@0 bs} → CRL.CertList bs → Set
helper₃ crl =
  case CRL.CertList.getIDP crl of λ
  where
    (_ , none) → ⊥
    (_ , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkIDPFieldsSeqFields distributionPoint onlyContainsUserCerts onlyContainsCACerts onlySomeReasons (mkDefault none notDefault) onlyContainsAttributeCerts notEmptyProp bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) → ⊥
    (_ , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkIDPFieldsSeqFields distributionPoint onlyContainsUserCerts onlyContainsCACerts onlySomeReasons (mkDefault (some (mkTLV len₂ (mkBoolValue true b vᵣ bs≡₅) len≡₂ bs≡₄)) notDefault) onlyContainsAttributeCerts notEmptyProp bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) → ⊤
    (_ , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkIDPFieldsSeqFields distributionPoint onlyContainsUserCerts onlyContainsCACerts onlySomeReasons (mkDefault (some (mkTLV len₂ (mkBoolValue false b vᵣ bs≡₅) len≡₂ bs≡₄)) notDefault) onlyContainsAttributeCerts notEmptyProp bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) → ⊥


---- verify issuer field in the CRL matches cRLIssuer in the DP
helper : ∀ {@0 bs₁ bs₂} → DistPoint bs₁ → CRL.CertList bs₂ → Set
helper (mkTLV len (mkDistPointFields crldp crldprsn none notOnlyReasonT bs≡₁) len≡ bs≡) crl = ⊥
helper (mkTLV len (mkDistPointFields crldp crldprsn (some (mkTLV len₁ (mk×ₚ fstₚ₁ sndₚ₁) len≡₁ bs≡₂)) notOnlyReasonT bs≡₁) len≡ bs≡) crl = helper₂ fstₚ₁
  where
  helper₂ : ∀ {@0 bs} → SequenceOf GeneralName bs → Set
  helper₂ nil = ⊥ --- ?
  helper₂ (cons (mkIListCons (dirname (mkTLV len issr len≡ bs≡₁)) tail₁ bs≡)) = NameMatch issr (CRL.CertList.getIssuer crl)
  helper₂ (cons (mkIListCons _ tail₁ bs≡)) = helper₂ tail₁



-- helper nil = ⊤
-- helper (cons (mkIListCons (mkTLV len (mkDistPointFields crldp crldprsn none notOnlyReasonT bs≡₂) len≡ bs≡₁) t bs≡)) = helper t
-- helper (cons (mkIListCons (mkTLV len (mkDistPointFields crldp crldprsn
          -- (some (mkTLV len₁ (mk×ₚ fstₚ₂ sndₚ₂) len≡₁ bs≡₃)) notOnlyReasonT bs≡₂) len≡ bs≡₁) t bs≡)) = helper₂ fstₚ₂ × helper t
          --   where
          --   helper₃ : Set
          --   helper₃ = case CRL.CertList.getIDP crl of λ where
          --       (_ , none) → ⊥
          --       (_ , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkIDPFieldsSeqFields distributionPoint onlyContainsUserCerts onlyContainsCACerts onlySomeReasons (mkDefault none notDefault) onlyContainsAttributeCerts notEmptyProp bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) → ⊥
          --       (_ , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkIDPFieldsSeqFields distributionPoint onlyContainsUserCerts onlyContainsCACerts onlySomeReasons (mkDefault (some (mkTLV len₂ (mkBoolValue true b vᵣ bs≡₅) len≡₂ bs≡₄)) notDefault) onlyContainsAttributeCerts notEmptyProp bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) → ⊤
          --       (_ , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkIDPFieldsSeqFields distributionPoint onlyContainsUserCerts onlyContainsCACerts onlySomeReasons (mkDefault (some (mkTLV len₂ (mkBoolValue false b vᵣ bs≡₅) len≡₂ bs≡₄)) notDefault) onlyContainsAttributeCerts notEmptyProp bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) → ⊥

          --   helper₂ : ∀ {@0 bs} → SequenceOf GeneralName bs → Set
          --   helper₂ nil = ⊤
          --   helper₂ (cons (mkIListCons (dirname (mkTLV len issr len≡ bs≡₁)) tail₁ bs≡)) = ((NameMatch issr (CRL.CertList.getIssuer crl)) × helper₃) × (helper₂ tail₁)
          --   helper₂ (cons (mkIListCons _ tail₁ bs≡)) = helper₂ tail₁
