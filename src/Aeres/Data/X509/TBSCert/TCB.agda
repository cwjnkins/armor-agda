{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.Extension.TCB
open import Aeres.Data.X509.PublicKey.TCB
import      Aeres.Data.X509.Name.TCB as Name
open import Aeres.Data.X509.SignAlg.TCB
open import Aeres.Data.X509.TBSCert.UID.TCB
import      Aeres.Data.X509.TBSCert.Version.TCB as Version
import      Aeres.Data.X509.Validity.TCB as Validity
open import Aeres.Data.X509.Validity.Time.TCB
import      Aeres.Data.X690-DER.Int.TCB as Int
import      Aeres.Data.X690-DER.SequenceOf as SequenceOf
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Option
import      Aeres.Grammar.Sum
import      Aeres.Grammar.Seq
import      Aeres.Grammar.Parallel
import      Aeres.Grammar.Definitions
open import Aeres.Prelude
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.TBSCert.TCB where

open Aeres.Grammar.Sum    UInt8
open Aeres.Grammar.Seq    UInt8
open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8
open Aeres.Grammar.Parallel    UInt8
open Int     hiding (getVal)
open Name     using  (Name)
open SequenceOf using (SequenceOf)
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

  getValidityStartTime : Time _
  getValidityEndTime : Time _

  getValidityStartTime = Validity.getNBTime validity
  getValidityEndTime   = Validity.getNATime validity

  -- getYearNB :  ℕ
  -- getYearNB = Validity.getYearNB validity
  -- getMonthNB :  ℕ
  -- getMonthNB = Validity.getMonthNB validity
  -- getDayNB :  ℕ
  -- getDayNB = Validity.getDayNB validity
  -- getHourNB :  ℕ
  -- getHourNB = Validity.getHourNB validity
  -- getMinNB :  ℕ
  -- getMinNB = Validity.getMinNB validity
  -- getSecNB :  ℕ
  -- getSecNB = Validity.getSecNB validity

  -- getYearNA :  ℕ
  -- getYearNA = Validity.getYearNA validity
  -- getMonthNA :  ℕ
  -- getMonthNA = Validity.getMonthNA validity
  -- getDayNA :  ℕ
  -- getDayNA = Validity.getDayNA validity
  -- getHourNA :  ℕ
  -- getHourNA = Validity.getHourNA validity
  -- getMinNA :  ℕ
  -- getMinNA = Validity.getMinNA validity
  -- getSecNA :  ℕ
  -- getSecNA = Validity.getSecNA validity

  -- getPublicKeyOIDbs : List UInt8
  -- getPublicKeyOIDbs = PublicKey.getPkAlgOIDbs pk

  getIssuerLen : ℕ
  getIssuerLen = SequenceOf.lengthSequence (TLV.val issuer)

  getSubjectLen :  ℕ
  getSubjectLen = SequenceOf.lengthSequence (TLV.val subject)

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

Rep₁ = &ₚ (Option SubUID) (Option Extensions)
Rep₂ = &ₚ (Option IssUID) Rep₁
Rep₃ = &ₚ (PublicKey ×ₚ Singleton) Rep₂
Rep₄ = &ₚ Name Rep₃
Rep₅ = &ₚ Validity Rep₄
Rep₆ = &ₚ Name Rep₅
Rep₇ = &ₚ SignAlg Rep₆

Rep : @0 List UInt8 → Set
Rep = (&ₚ (&ₚ (Option Version) Int) Rep₇)

equivalentTBSCertFields : Equivalent
               Rep
               TBSCertFields
proj₁ equivalentTBSCertFields (mk&ₚ (mk&ₚ fstₚ₁ sndₚ₁ refl) (mk&ₚ fstₚ₂ (mk&ₚ fstₚ₃ (mk&ₚ fstₚ₄ (mk&ₚ fstₚ₅ (mk&ₚ (mk×ₚ fstₚ₆ s) (mk&ₚ fstₚ₇ (mk&ₚ fstₚ₈ sndₚ₂ refl) refl) refl) refl) refl) refl) refl) bs≡) =
  mkTBSCertFields fstₚ₁ sndₚ₁ fstₚ₂ fstₚ₃ fstₚ₄ fstₚ₅ fstₚ₆ s fstₚ₇ fstₚ₈ sndₚ₂
    (trans₀ bs≡ (solve (++-monoid UInt8)))
proj₂ equivalentTBSCertFields (mkTBSCertFields version serial signAlg issuer validity subject pk pkBytes issuerUID subjectUID extensions bs≡) =
  mk&ₚ (mk&ₚ version serial refl) (mk&ₚ signAlg (mk&ₚ issuer (mk&ₚ validity (mk&ₚ subject (mk&ₚ (mk×ₚ pk pkBytes) (mk&ₚ issuerUID (mk&ₚ subjectUID extensions refl) refl) refl) refl) refl) refl) refl)
    (trans₀ bs≡ (solve (++-monoid UInt8)))
