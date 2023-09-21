{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.Extension.TCB
open import Aeres.Data.X509.PublicKey.TCB
import      Aeres.Data.X509.RDN.TCB as RDN
open import Aeres.Data.X509.SignAlg.TCB
open import Aeres.Data.X509.TBSCert.UID.TCB
import      Aeres.Data.X509.TBSCert.Version.TCB as Version
import      Aeres.Data.X509.Validity.TCB as Validity
import      Aeres.Data.X690-DER.Int.TCB as Int
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Data.X690-DER.Time.TCB
import      Aeres.Grammar.Option
open import Aeres.Prelude

module Aeres.Data.X509.TBSCert.TCB where

open Aeres.Grammar.Option UInt8
open Int     hiding (getVal)
open RDN     using  (RDN; Name)
open Validity using (Validity)
open Version hiding (getVal)

record TBSCertFields (@0 bs : List UInt8) : Set where
  constructor mkTBSCertFields
  field
    @0 {ver ser sa i va u p u₁ u₂ e} : List UInt8
    version : Option Version ver
    serial  : Int ser
    signAlg : SignAlg sa
    issuer  : Name i
    validity : Validity va
    subject  : Name u
    pk       : PublicKey p
    pkBytes  : Singleton p -- TODO: eventually this should come from serialization
    issuerUID : Option IssUID u₁ -- if this takes a lot of time, this and the lower can be dropped
    subjectUID : Option SubUID u₂
    extensions : Option Extensions e
    @0 bs≡  : bs ≡ ver ++ ser ++ sa ++ i ++ va ++ u ++ p ++ u₁ ++ u₂ ++ e

  getVersion : ℤ
  getVersion = elimOption{X = const ℤ} (ℤ.+ 0) (λ v → Version.getVal v) version

  getSerial : ℤ
  getSerial = Int.getVal serial

  getValidityStartTime getValidityEndTime : Exists─ (List UInt8) Time

  getValidityStartTime = Validity.getStartTime validity
  getValidityEndTime   = Validity.getEndTime validity

  getYearNB :  ℕ
  getYearNB = Validity.getYearNB validity
  getMonthNB :  ℕ
  getMonthNB = Validity.getMonthNB validity
  getDayNB :  ℕ
  getDayNB = Validity.getDayNB validity
  getHourNB :  ℕ
  getHourNB = Validity.getHourNB validity
  getMinNB :  ℕ
  getMinNB = Validity.getMinNB validity
  getSecNB :  ℕ
  getSecNB = Validity.getSecNB validity

  getYearNA :  ℕ
  getYearNA = Validity.getYearNA validity
  getMonthNA :  ℕ
  getMonthNA = Validity.getMonthNA validity
  getDayNA :  ℕ
  getDayNA = Validity.getDayNA validity
  getHourNA :  ℕ
  getHourNA = Validity.getHourNA validity
  getMinNA :  ℕ
  getMinNA = Validity.getMinNA validity
  getSecNA :  ℕ
  getSecNA = Validity.getSecNA validity

  -- getPublicKeyOIDbs : List UInt8
  -- getPublicKeyOIDbs = PublicKey.getPkAlgOIDbs pk

  getIssuerLen : ℕ
  getIssuerLen = RDN.getSeqLen issuer

  getSubjectLen :  ℕ
  getSubjectLen = RDN.getSeqLen subject

  getIssuer : Exists─ (List UInt8) Name
  getIssuer = _ , issuer

  getSubject : Exists─ (List UInt8) Name
  getSubject = _ , subject

  getSignAlg : Exists─ (List UInt8) SignAlg
  getSignAlg = _ , signAlg

  getBC : Exists─ (List UInt8) (Option ExtensionFieldBC)
  getBC = elimOption (_ , none) (λ v → Extensions.getBC v) extensions

  getKU : Exists─ (List UInt8) (Option ExtensionFieldKU)
  getKU = elimOption (_ , none) (λ v → Extensions.getKU v) extensions

  getEKU : Exists─ (List UInt8) (Option ExtensionFieldEKU)
  getEKU = elimOption (_ , none) (λ v → Extensions.getEKU v) extensions

  getSAN : Exists─ (List UInt8) (Option ExtensionFieldSAN)
  getSAN = elimOption (_ , none) (λ v → Extensions.getSAN v) extensions

  getCRLDIST : Exists─ (List UInt8) (Option ExtensionFieldCRLDist)
  getCRLDIST = elimOption (_ , none) (λ v → Extensions.getCRLDIST v) extensions

  getCPOL : Exists─ (List UInt8) (Option ExtensionFieldCPOL)
  getCPOL = elimOption (_ , none) (λ v → Extensions.getCPOL v) extensions

  getExtensionsList : List (Exists─ (List UInt8) Extension)
  getExtensionsList = elimOption [] (λ v → Extensions.getExtensionsList v) extensions

TBSCert : (@0 _ : List UInt8) → Set
TBSCert xs = TLV Tag.Sequence TBSCertFields xs

