open import Armor.Binary
open import Armor.Data.X509.SignAlg.TCB
open import Armor.Data.X509.Name.TCB
open import Armor.Data.X509.CRL.TBSCertList.TCB
open import Armor.Data.X690-DER.BitString.TCB
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Data.X690-DER.Tag as Tag
open import Armor.Data.X690-DER.OctetString.TCB
import      Armor.Grammar.IList.TCB
import      Armor.Grammar.Definitions
import      Armor.Grammar.Seq
import Armor.Grammar.Parallel.TCB
open import Armor.Prelude
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Armor.Data.X509.CRL.CertList.TCB where

open Armor.Grammar.Seq    UInt8
open Armor.Grammar.IList.TCB    UInt8
open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Parallel.TCB UInt8

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

  getIssuer : Name ?
  getIssuer = {!!}

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
