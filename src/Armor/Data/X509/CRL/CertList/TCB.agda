open import Armor.Binary
open import Armor.Data.X509.SignAlg.TCB
open import Armor.Data.X509.Name.TCB
open import Armor.Data.X509.CRL.TBSCertList.TCB
open import Armor.Data.X509.CRL.RevokedCertificates.TCB
open import Armor.Data.X509.CRL.Extension.TCB
open import Armor.Data.X690-DER.BitString.TCB
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Data.X690-DER.Tag as Tag
open import Armor.Data.X690-DER.OctetString.TCB
import      Armor.Grammar.IList.TCB
import      Armor.Grammar.Definitions
import      Armor.Grammar.Seq
import Armor.Grammar.Parallel.TCB
import Armor.Grammar.Option.TCB
open import Armor.Prelude
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Armor.Data.X509.CRL.CertList.TCB where

open Armor.Grammar.Seq    UInt8
open Armor.Grammar.IList.TCB    UInt8
open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Parallel.TCB UInt8
open Armor.Grammar.Option.TCB UInt8

-- CertificateList  ::=  SEQUENCE  {
--         tbsCertList          TBSCertList,
--         signatureAlgorithm   AlgorithmIdentifier,
--         signatureValue       BIT STRING  }

record CertListFields (@0 bs : List UInt8) : Set where
  constructor mkCertListFields
  field
    @0 {t sa sig} : List UInt8
    tbs : TBSCertList t
    tbsBytes : Singleton t
    signAlg : SignAlg sa
    signature : BitString sig
    signatureBytes : Singleton sig
    @0 bs≡  : bs ≡ t ++ sa ++ sig

  getIssuer :  Name (TBSCertListFields.i (TLV.val tbs))
  getIssuer = TBSCertListFields.issuer (TLV.val tbs)

  getRevokedCertificateList : List (Exists─ (List UInt8) RevokedCertificate)
  getRevokedCertificateList = TBSCertListFields.getRevokedCertificateList (TLV.val tbs)

  getIDP : Exists─ (List UInt8) (Option ExtensionFieldIDP)
  getIDP = TBSCertListFields.getIDP (TLV.val tbs)

  getDCRLI : Exists─ (List UInt8) (Option ExtensionFieldDCRLI)
  getDCRLI = TBSCertListFields.getDCRLI (TLV.val tbs)

  getAKI : Exists─ (List UInt8) (Option ExtensionFieldAKI)
  getAKI = TBSCertListFields.getAKI (TLV.val tbs)

CertList : (@0 _ : List UInt8) → Set
CertList xs = TLV Tag.Sequence  CertListFields xs

CertListFieldsRep : @0 List UInt8 → Set
CertListFieldsRep = &ₚ (TBSCertList ×ₚ Singleton) (&ₚ SignAlg (BitString ×ₚ Singleton))

equivalentCertListFields : Equivalent CertListFieldsRep CertListFields
proj₁ equivalentCertListFields (mk&ₚ (mk×ₚ fstₚ₁ s) (mk&ₚ fstₚ₂ (mk×ₚ sndₚ₁ s') refl) bs≡) =
  mkCertListFields fstₚ₁ s fstₚ₂ sndₚ₁ s' bs≡
proj₂ equivalentCertListFields (mkCertListFields tbs tbsBytes signAlg signature signatureBytes bs≡)
  = mk&ₚ (mk×ₚ tbs tbsBytes) (mk&ₚ signAlg (mk×ₚ signature signatureBytes) refl) bs≡

RawCertListFieldsRep : Raw CertListFieldsRep
RawCertListFieldsRep = Raw&ₚ (Raw×ₚ RawTBSCertList RawOctetStringValue)
                      (Raw&ₚ RawSignAlg (Raw×ₚ RawBitString RawOctetStringValue))

RawCertListFields : Raw CertListFields
RawCertListFields = Iso.raw equivalentCertListFields RawCertListFieldsRep

RawCertList : Raw CertList
RawCertList = RawTLV _ RawCertListFields


module CertList where
  getTBSCertList : ∀{@0 bs} → (c : CertList bs) → TBSCertList (CertListFields.t (TLV.val c))
  getTBSCertList c = CertListFields.tbs (TLV.val c)

  getIssuer : ∀{@0 bs} → (c : CertList bs) → Name (TBSCertListFields.i (TLV.val (getTBSCertList c)))
  getIssuer c = CertListFields.getIssuer (TLV.val c)

  getRevokedCertificateList :  ∀{@0 bs} → (c : CertList bs) → List (Exists─ (List UInt8) RevokedCertificate)
  getRevokedCertificateList c = CertListFields.getRevokedCertificateList (TLV.val c)

  getIDP :  ∀{@0 bs} → (c : CertList bs)  → Exists─ (List UInt8) (Option ExtensionFieldIDP)
  getIDP c = CertListFields.getIDP (TLV.val c)

  getDCRLI :  ∀{@0 bs} → (c : CertList bs)  → Exists─ (List UInt8) (Option ExtensionFieldDCRLI)
  getDCRLI c = CertListFields.getDCRLI (TLV.val c)

  getAKI :  ∀{@0 bs} → (c : CertList bs)  → Exists─ (List UInt8) (Option ExtensionFieldAKI)
  getAKI c = CertListFields.getAKI (TLV.val c)

  isDeltaCRL : ∀{@0 bs} → (c : CertList bs) → Set
  isDeltaCRL c =
    case getDCRLI c of λ where
      (─ .[] , none) → ⊥
      (fst , some x) → ⊤

  isNotDeltaCRL : ∀{@0 bs} → (c : CertList bs) → Set
  isNotDeltaCRL c =
    case getDCRLI c of λ where
      (─ .[] , none) → ⊤
      (fst , some x) → ⊥
