{-# OPTIONS --erasure #-}
open import Armor.Binary
open import Armor.Data.X509.SignAlg.TCB
open import Armor.Data.X509.Name.TCB
open import Armor.Data.X509.Validity.Time.TCB
open import Armor.Data.X690-DER.BitString.TCB
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Data.X690-DER.Tag as Tag
open import Armor.Data.X509.CRL.Version.TCB
open import Armor.Data.X509.CRL.Extension.TCB
import      Armor.Data.X509.Validity.TCB as Validity
open import Armor.Data.X509.CRL.RevokedCertificates.TCB
import      Armor.Grammar.IList.TCB
import      Armor.Grammar.Definitions
import      Armor.Grammar.Seq
import      Armor.Grammar.Option
open import Armor.Prelude
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Armor.Data.X509.CRL.TBSCertList.TCB where

open Armor.Grammar.Seq    UInt8
open Armor.Grammar.IList.TCB    UInt8
open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8
open Validity using (Validity)

-- TBSCertList  ::=  SEQUENCE  {
--      version                 Version OPTIONAL,
--                                   -- if present, MUST be v2
--      signature               AlgorithmIdentifier,
--      issuer                  Name,
--      thisUpdate              Time,
--      nextUpdate              Time OPTIONAL,
--      revokedCertificates     SEQUENCE OF SEQUENCE  {
--           userCertificate         CertificateSerialNumber,
--           revocationDate          Time,
--           crlEntryExtensions      Extensions OPTIONAL
--                                    -- if present, version MUST be v2
--                                }  OPTIONAL,
--      crlExtensions           [0]  EXPLICIT Extensions OPTIONAL
--                                    -- if present, version MUST be v2
--                                }

record TBSCertListFields (@0 bs : List UInt8) : Set where
  constructor mkTBSCertListFields
  field
    @0 {ver sa i tu nu r e} : List UInt8
    version : Option Version ver
    signAlg : SignAlg sa
    issuer  : Name i
    thisUpdate : Time tu
    nextUpdate : Option Time nu
    revokedCertificates : Option RevokedCertificates r
    crlExtensions : Option Extensions e
    @0 bs≡  : bs ≡ ver ++ sa ++ i ++ tu ++ nu ++ r ++ e

  getSignAlg : SignAlg sa
  getSignAlg = signAlg

  getIDP : Exists─ (List UInt8) (Option ExtensionFieldIDP)
  getIDP = elimOption (_ , none) (λ v → Extensions.getIDP v) crlExtensions

  getDCRLI : Exists─ (List UInt8) (Option ExtensionFieldDCRLI)
  getDCRLI = elimOption (_ , none) (λ v → Extensions.getDCRLI v) crlExtensions

  getAKI : Exists─ (List UInt8) (Option ExtensionFieldAKI)
  getAKI = elimOption (_ , none) (λ v → Extensions.getAKI v) crlExtensions

  getFCRL : Exists─ (List UInt8) (Option ExtensionFieldFCRL)
  getFCRL = elimOption (_ , none) (λ v → Extensions.getFCRL v) crlExtensions

  getRevokedCertificateList : List (Exists─ (List UInt8) RevokedCertificate)
  getRevokedCertificateList = elimOption [] (λ v → RevokedCertificates.getRevokedCertificates v) revokedCertificates

  getCRLExtensionsList : List (Exists─ (List UInt8) Extension)
  getCRLExtensionsList = elimOption [] (λ v → Extensions.getExtensionsList v) crlExtensions

  getThisUpdate : Time tu
  getThisUpdate = thisUpdate

  getNextUpdate : Option Time nu
  getNextUpdate = nextUpdate

TBSCertList : (@0 _ : List UInt8) → Set
TBSCertList xs = TLV Tag.Sequence TBSCertListFields xs

Rep₁ = &ₚ (Option RevokedCertificates) (Option Extensions)
Rep₂ = &ₚ (Option Time) Rep₁
Rep₃ = &ₚ Time Rep₂
Rep₄ = &ₚ Name Rep₃
Rep₅ = &ₚ (Option Version) SignAlg
Rep₆ = &ₚ Rep₅ Rep₄

TBSCertListFieldsRep : @0 List UInt8 → Set
TBSCertListFieldsRep = Rep₆

equivalentTBSCertListFields : Equivalent TBSCertListFieldsRep TBSCertListFields
proj₁ equivalentTBSCertListFields (mk&ₚ(mk&ₚ version signAlg refl)
      (mk&ₚ issuer
        (mk&ₚ thisUpdate
          (mk&ₚ nextUpdate
            (mk&ₚ revokedCertificates crlExtensions refl) refl) refl) refl) bs≡) =
  mkTBSCertListFields version signAlg issuer thisUpdate nextUpdate revokedCertificates crlExtensions (trans₀ bs≡ (solve (++-monoid UInt8)))
proj₂ equivalentTBSCertListFields (mkTBSCertListFields version signAlg issuer thisUpdate nextUpdate revokedCertificates crlExtensions bs≡) =
  mk&ₚ(mk&ₚ version signAlg refl)
      (mk&ₚ issuer
        (mk&ₚ thisUpdate
          (mk&ₚ nextUpdate
            (mk&ₚ revokedCertificates crlExtensions refl) refl) refl) refl) (trans₀ bs≡ (solve (++-monoid UInt8)))

RawTBSCertListFieldsRep : Raw TBSCertListFieldsRep
RawTBSCertListFieldsRep = Raw&ₚ (Raw&ₚ (RawOption RawVersion) RawSignAlg)
                         (Raw&ₚ RawName
                         (Raw&ₚ RawTime
                         (Raw&ₚ (RawOption RawTime)
                         (Raw&ₚ (RawOption RawRevokedCertificates)
                                 (RawOption RawExtensions)))))

RawTBSCertListFields = Iso.raw equivalentTBSCertListFields RawTBSCertListFieldsRep

RawTBSCertList : Raw TBSCertList
RawTBSCertList = RawTLV _ RawTBSCertListFields
