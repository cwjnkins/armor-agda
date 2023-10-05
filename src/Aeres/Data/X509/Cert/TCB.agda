{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.Extension.TCB
open import Aeres.Data.X509.RDN.TCB
open import Aeres.Data.X509.SignAlg.TCB
open import Aeres.Data.X509.TBSCert.TCB
import      Aeres.Data.X509.TBSCert.UID.TCB as TBSCert
open import Aeres.Data.X509.Validity.TCB
open import Aeres.Data.X509.Validity.Time.TCB
import      Aeres.Data.X690-DER.BitString.Serializer as BitString
open import Aeres.Data.X690-DER.BitString.TCB
open import Aeres.Data.X690-DER.Int.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Data.X690-DER.SequenceOf
open import Aeres.Data.X690-DER.OID
import      Aeres.Grammar.IList.TCB
import      Aeres.Grammar.Option.TCB
import      Aeres.Grammar.Parallel.TCB
open import Aeres.Prelude

module Aeres.Data.X509.Cert.TCB where

open Aeres.Grammar.IList.TCB    UInt8
open Aeres.Grammar.Option.TCB   UInt8
open Aeres.Grammar.Parallel.TCB UInt8

record CertFields (@0 bs : List UInt8) : Set where
  constructor mkCertFields
  field
    @0 {t sa sig} : List UInt8
    tbs : TBSCert t
    tbsBytes : Singleton t    -- TODO: eventually this should come from serialization
    signAlg : SignAlg sa
    signature : BitString sig
    signatureBytes : Singleton sig
    @0 bs≡  : bs ≡ t ++ sa ++ sig

  getVersion : ℤ
  getVersion = TBSCertFields.getVersion (TLV.val tbs)

  getSerial : ℤ
  getSerial = TBSCertFields.getSerial (TLV.val tbs)

  getValidity : Validity _
  getValidity = TBSCertFields.validity (TLV.val tbs)

  getValidityStartTime : Time _
  getValidityEndTime   : Time _

  getValidityStartTime = TBSCertFields.getValidityStartTime ∘ TLV.val $ tbs
  getValidityEndTime   = TBSCertFields.getValidityEndTime  ∘ TLV.val $ tbs 

  -- getYearNB :  ℕ
  -- getYearNB = TBSCertFields.getYearNB (TLV.val tbs)
  -- getMonthNB :  ℕ
  -- getMonthNB = TBSCertFields.getMonthNB (TLV.val tbs)
  -- getDayNB :  ℕ
  -- getDayNB = TBSCertFields.getDayNB (TLV.val tbs)
  -- getHourNB :  ℕ
  -- getHourNB = TBSCertFields.getHourNB (TLV.val tbs)
  -- getMinNB :  ℕ
  -- getMinNB = TBSCertFields.getMinNB (TLV.val tbs)
  -- getSecNB :  ℕ
  -- getSecNB = TBSCertFields.getSecNB (TLV.val tbs)

  -- getYearNA :  ℕ
  -- getYearNA = TBSCertFields.getYearNA (TLV.val tbs)
  -- getMonthNA :  ℕ
  -- getMonthNA = TBSCertFields.getMonthNA (TLV.val tbs)
  -- getDayNA :  ℕ
  -- getDayNA = TBSCertFields.getDayNA (TLV.val tbs)
  -- getHourNA :  ℕ
  -- getHourNA = TBSCertFields.getHourNA (TLV.val tbs)
  -- getMinNA :  ℕ
  -- getMinNA = TBSCertFields.getMinNA (TLV.val tbs)
  -- getSecNA :  ℕ
  -- getSecNA = TBSCertFields.getSecNA (TLV.val tbs)

  getIssuerLen :  ℕ
  getIssuerLen = TBSCertFields.getIssuerLen (TLV.val tbs)

  getSubjectLen :  ℕ
  getSubjectLen = TBSCertFields.getSubjectLen (TLV.val tbs)

  getIssuer :  Exists─ (List UInt8) Name
  getIssuer = TBSCertFields.getIssuer (TLV.val tbs)

  getSubject :  Exists─ (List UInt8) Name
  getSubject = TBSCertFields.getSubject (TLV.val tbs)

  getIssUID : Exists─ (List UInt8) (Option TBSCert.IssUID)
  getIssUID = _ , (TBSCertFields.issuerUID (TLV.val tbs))

  getSubUID : Exists─ (List UInt8) (Option TBSCert.SubUID)
  getSubUID = _ , (TBSCertFields.subjectUID (TLV.val tbs))

  getTBSCertSignAlg : Exists─ (List UInt8) SignAlg
  getTBSCertSignAlg = TBSCertFields.getSignAlg (TLV.val tbs)

  getCertSignAlg : Exists─ (List UInt8) SignAlg
  getCertSignAlg =  _ , signAlg

  getBC : Exists─ (List UInt8) (Option ExtensionFieldBC)
  getBC = TBSCertFields.getBC (TLV.val tbs)

  getKU : Exists─ (List UInt8) (Option ExtensionFieldKU)
  getKU = TBSCertFields.getKU (TLV.val tbs)

  getEKU : Exists─ (List UInt8) (Option ExtensionFieldEKU)
  getEKU = TBSCertFields.getEKU (TLV.val tbs)

  getSAN : Exists─ (List UInt8) (Option ExtensionFieldSAN)
  getSAN = TBSCertFields.getSAN (TLV.val tbs)

  getCRLDIST : Exists─ (List UInt8) (Option ExtensionFieldCRLDist)
  getCRLDIST = TBSCertFields.getCRLDIST (TLV.val tbs)

  getCPOL : Exists─ (List UInt8) (Option ExtensionFieldCPOL)
  getCPOL = TBSCertFields.getCPOL (TLV.val tbs)

  getExtensions : Exists─ (List UInt8) (Option Extensions)
  getExtensions = _ , (TBSCertFields.extensions (TLV.val tbs))
  
  getExtensionsList : List (Exists─ (List UInt8) Extension)
  getExtensionsList = TBSCertFields.getExtensionsList (TLV.val tbs)

  getPublicKeyBytes : List UInt8
  getPublicKeyBytes = ↑ (TBSCertFields.pkBytes (TLV.val tbs))

module Cert where
  Cert : (@0 _ : List UInt8) → Set
  Cert xs = TLV Tag.Sequence  CertFields xs

  module _ {@0 bs} (c : Cert bs) where
    getVersion : ℤ
    getVersion = CertFields.getVersion (TLV.val c)

    getSerial : ℤ
    getSerial = CertFields.getSerial (TLV.val c)

    getTBSBytes : List UInt8
    getTBSBytes = ↑ (CertFields.tbsBytes (TLV.val c))

    getValidity : Validity _
    getValidity = CertFields.getValidity (TLV.val c)

    getValidityStartTime : Time _
    getValidityEndTime   : Time _

    getValidityStartTime = CertFields.getValidityStartTime ∘ TLV.val $ c
    getValidityEndTime   = CertFields.getValidityEndTime   ∘ TLV.val $ c

    -- getYearNB :  ℕ
    -- getYearNB = CertFields.getYearNB (TLV.val c)
    -- getMonthNB :  ℕ
    -- getMonthNB = CertFields.getMonthNB (TLV.val c)
    -- getDayNB :  ℕ
    -- getDayNB = CertFields.getDayNB (TLV.val c)
    -- getHourNB :  ℕ
    -- getHourNB = CertFields.getHourNB (TLV.val c)
    -- getMinNB :  ℕ
    -- getMinNB = CertFields.getMinNB (TLV.val c)
    -- getSecNB :  ℕ
    -- getSecNB = CertFields.getSecNB (TLV.val c)

    -- getYearNA :  ℕ
    -- getYearNA = CertFields.getYearNA (TLV.val c)
    -- getMonthNA :  ℕ
    -- getMonthNA = CertFields.getMonthNA (TLV.val c)
    -- getDayNA :  ℕ
    -- getDayNA = CertFields.getDayNA (TLV.val c)
    -- getHourNA :  ℕ
    -- getHourNA = CertFields.getHourNA (TLV.val c)
    -- getMinNA :  ℕ
    -- getMinNA = CertFields.getMinNA (TLV.val c)
    -- getSecNA :  ℕ
    -- getSecNA = CertFields.getSecNA (TLV.val c)

    getIssuerLen :  ℕ
    getIssuerLen = CertFields.getIssuerLen (TLV.val c)

    getSubjectLen :  ℕ
    getSubjectLen = CertFields.getSubjectLen (TLV.val c)

    getIssuer :  Exists─ (List UInt8) Name
    getIssuer = CertFields.getIssuer (TLV.val c)

    getSubject :  Exists─ (List UInt8) Name
    getSubject = CertFields.getSubject (TLV.val c)

    getIssUID : Exists─ (List UInt8) (Option TBSCert.IssUID)
    getIssUID = CertFields.getIssUID (TLV.val c)

    getSubUID : Exists─ (List UInt8) (Option TBSCert.SubUID)
    getSubUID = CertFields.getSubUID (TLV.val c)

    getTBSCertSignAlg : Exists─ (List UInt8) SignAlg
    getTBSCertSignAlg = CertFields.getTBSCertSignAlg (TLV.val c)

    getCertSignAlg : Exists─ (List UInt8) SignAlg
    getCertSignAlg = CertFields.getCertSignAlg (TLV.val c)

    -- getPublicKeyOIDbs : List UInt8
    -- getPublicKeyOIDbs = TBSCertFields.getPublicKeyOIDbs (TLV.val (CertFields.tbs (TLV.val c)))

    getBC : Exists─ (List UInt8) (Option ExtensionFieldBC)
    getBC = CertFields.getBC (TLV.val c)

    getKU : Exists─ (List UInt8) (Option ExtensionFieldKU)
    getKU = CertFields.getKU (TLV.val c)

    getEKU : Exists─ (List UInt8) (Option ExtensionFieldEKU)
    getEKU = CertFields.getEKU (TLV.val c)

    getSAN : Exists─ (List UInt8) (Option ExtensionFieldSAN)
    getSAN = CertFields.getSAN (TLV.val c)

    getCRLDIST : Exists─ (List UInt8) (Option ExtensionFieldCRLDist)
    getCRLDIST = CertFields.getCRLDIST (TLV.val c)

    getCPOL : Exists─ (List UInt8) (Option ExtensionFieldCPOL)
    getCPOL = CertFields.getCPOL (TLV.val c)

    getExtensions : Exists─ (List UInt8) (Option Extensions)
    getExtensions = CertFields.getExtensions (TLV.val c)

    getExtensionsList : List (Exists─ (List UInt8) Extension)
    getExtensionsList = CertFields.getExtensionsList (TLV.val c)

    getPublicKeyBytes : List UInt8
    getPublicKeyBytes = CertFields.getPublicKeyBytes (TLV.val c)

    getSignatureBytes : List UInt8
    getSignatureBytes = ↑ CertFields.signatureBytes (TLV.val c)

    getSignatureValueBytes : List UInt8
    getSignatureValueBytes = ↑ (BitString.serializeValue (TLV.val (CertFields.signature (TLV.val c))))

    -- List of EKU OIds to List of List UInt8
    getEKUOIDList : Exists─ (List UInt8) (Option ExtensionFieldEKU) → List (List UInt8)
    getEKUOIDList (─ .[] , none) = []
    getEKUOIDList (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ val len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = helper (fstₚ val)
      where
      helper : ∀ {@0 bs} → SequenceOf OID bs → List (List UInt8)
      helper nil = []
      helper (cons (mkIListCons head₁ tail₁ bs≡)) = (↑ (OID.serialize head₁)) ∷ (helper tail₁)

open Cert public using (Cert)

module Chain where
  Chain : (@0 _ : List UInt8) → Set
  Chain = IList Cert
open Chain public using (Chain)
