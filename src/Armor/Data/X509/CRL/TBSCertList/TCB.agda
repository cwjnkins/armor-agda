open import Armor.Binary
open import Armor.Data.X509.SignAlg.TCB
open import Armor.Data.X509.Name.TCB
open import Armor.Data.X509.Validity.Time.TCB
open import Armor.Data.X690-DER.BitString.TCB
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Data.X690-DER.Tag as Tag
open import Armor.Data.X509.CRL.Version.TCB
open import Armor.Data.X509.CRL.Extension.TCB
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

TBSCertList : (@0 _ : List UInt8) → Set
TBSCertList xs = TLV Tag.Sequence TBSCertListFields xs

Rep₁ = &ₚ (Option RevokedCertificates) (Option Extensions)
Rep₂ = &ₚ (Option Time) Rep₁
Rep₃ = &ₚ Time Rep₂
Rep₄ = &ₚ Name Rep₃

TBSCertListFieldsRep : @0 List UInt8 → Set
TBSCertListFieldsRep = (&ₚ (&ₚ(Option Version) SignAlg) Rep₄)

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
RawTBSCertListFieldsRep = Raw&ₚ (Raw&ₚ (RawOption RawVersion) RawSignAlg) (Raw&ₚ RawName (Raw&ₚ RawTime
                        (Raw&ₚ (RawOption RawTime) (Raw&ₚ (RawOption RawRevokedCertificates) (RawOption RawExtensions)))))

RawTBSCertList : Raw TBSCertList
RawTBSCertList = RawTLV _ (Iso.raw equivalentTBSCertListFields RawTBSCertListFieldsRep)
