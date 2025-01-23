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
-- open import Armor.Data.X509.Semantic.Cert.Utils
open import Armor.Data.X509.Extension.CRLDistPoint.DistPoint.TCB as DP
open import Armor.Data.X509.GeneralNames.GeneralName.TCB
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
open import Armor.Grammar.IList as IList
import      Armor.Grammar.Parallel.TCB
open import Armor.Prelude

module Armor.Data.X509.CRL.Semantic.Utils where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8
open Armor.Grammar.Parallel.TCB UInt8

-- Revocation reason enumeration
data RevocationReason : Set where
  allReasons          : RevocationReason
  keyCompromise       : RevocationReason
  cACompromise        : RevocationReason
  affiliationChanged  : RevocationReason
  superseded          : RevocationReason
  cessationOfOperation : RevocationReason
  certificateHold     : RevocationReason
  privilegeWithdrawn  : RevocationReason
  aACompromise        : RevocationReason

-- Function to map a boolean list to revocation reasons
boolListToReasons : List Bool → List RevocationReason
boolListToReasons bools = selectReason₁ bools
  where
    -- Helper function to select reasons based on the Boolean value
    selectReason₉ : List Bool  → List RevocationReason
    selectReason₉ [] = []
    selectReason₉ (#0 ∷ x₁) = []
    selectReason₉ (#1 ∷ x₁) = [ aACompromise ]

    selectReason₈ : List Bool  → List RevocationReason
    selectReason₈ [] = []
    selectReason₈ (#0 ∷ x₁) = selectReason₉ x₁
    selectReason₈ (#1 ∷ x₁) = [ privilegeWithdrawn ] ++ selectReason₉ x₁

    selectReason₇ : List Bool  → List RevocationReason
    selectReason₇ [] = []
    selectReason₇ (#0 ∷ x₁) = selectReason₈ x₁
    selectReason₇ (#1 ∷ x₁) = [ certificateHold ] ++ selectReason₈ x₁

    selectReason₆ : List Bool  → List RevocationReason
    selectReason₆ [] = []
    selectReason₆ (#0 ∷ x₁) = selectReason₇ x₁
    selectReason₆ (#1 ∷ x₁) = [ cessationOfOperation ] ++ selectReason₇ x₁

    selectReason₅ : List Bool  → List RevocationReason
    selectReason₅ [] = []
    selectReason₅ (#0 ∷ x₁) = selectReason₆ x₁
    selectReason₅ (#1 ∷ x₁) = [ superseded ] ++ selectReason₆ x₁

    selectReason₄ : List Bool  → List RevocationReason
    selectReason₄ [] = []
    selectReason₄ (#0 ∷ x₁) = selectReason₅ x₁
    selectReason₄ (#1 ∷ x₁) = [ affiliationChanged ] ++ selectReason₅ x₁
    
    selectReason₃ : List Bool  → List RevocationReason
    selectReason₃ [] = []
    selectReason₃ (#0 ∷ x₁) = selectReason₄ x₁
    selectReason₃ (#1 ∷ x₁) = [ cACompromise ] ++ selectReason₄ x₁

    selectReason₂ : List Bool  → List RevocationReason
    selectReason₂ [] = []
    selectReason₂ (#0 ∷ x₁) = selectReason₃ x₁
    selectReason₂ (#1 ∷ x₁) = [ keyCompromise ] ++ selectReason₃ x₁
    
    selectReason₁ : List Bool  → List RevocationReason
    selectReason₁ [] = []
    selectReason₁ (x ∷ x₁) = selectReason₂ x₁

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

-- inputCheck : ∀{@0 bs₁ bs₂} → CRL.CertList bs₁ → Maybe (CRL.CertList bs₂) → Set
-- inputCheck crl (just delta) = CRL.CertList.isNotDeltaCRL crl × CRL.CertList.isDeltaCRL delta
-- inputCheck crl nothing = CRL.CertList.isNotDeltaCRL crl

record RevInputs : Set where
  constructor mkRevInputs
  field
    @0 {c cr de} : List UInt8
    cert : Cert c
    crl : CRL.CertList cr
    delta : Maybe (CRL.CertList de)
    useDeltas   : Bool
    -- @0 check : inputCheck crl delta
