open import Armor.Binary
open import Armor.Data.X509.CRL.CertList.TCB
open import Armor.Data.X509.SignAlg
open import Armor.Data.X509.CRL.TBSCertList
open import Armor.Data.X690-DER.BitString
open import Armor.Data.X690-DER.OctetString
open import Armor.Data.X690-DER.SequenceOf
open import Armor.Data.X690-DER.TLV
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions
import      Armor.Grammar.IList
import      Armor.Grammar.Option
import      Armor.Grammar.Parallel
import      Armor.Grammar.Seq
open import Armor.Prelude

module Armor.Data.X509.CRL.CertList.Properties where

open Armor.Grammar.Definitions  UInt8
open Armor.Grammar.IList        UInt8
open Armor.Grammar.Option       UInt8
open Armor.Grammar.Parallel     UInt8
open Armor.Grammar.Seq          UInt8

iso   : Iso CertListFieldsRep CertListFields
proj₁ iso = equivalentCertListFields
proj₁ (proj₂ iso) (mk&ₚ (mk×ₚ fstₚ₁ s) (mk&ₚ fstₚ₂ (mk×ₚ sndₚ₁ _) refl) refl) = refl
proj₂ (proj₂ iso) (mkCertListFields tbs tbsBytes signAlg signature sbytes refl) = refl

RawRep₁ = Raw&ₚ RawSignAlg (Raw×ₚ RawBitString RawOctetStringValue)
RawRep = Raw&ₚ (Raw×ₚ RawTBSCertList RawOctetStringValue) RawRep₁

@0 unambiguous : Unambiguous CertList
unambiguous =
  TLV.unambiguous (Iso.unambiguous iso
    (Seq.unambiguous
      (Parallel.unambiguous (TBSCertList.unambiguous) (λ where _ self self → refl))
      (Parallel.nosubstrings₁ TLV.nosubstrings)
      (Seq.unambiguous SignAlg.unambiguous SignAlg.nosubstrings
        (Parallel.unambiguous BitString.unambiguous (λ where _ self self → refl)))))

@0 nonmalleableFields : NonMalleable RawCertListFields
nonmalleableFields =
  Iso.nonmalleable iso RawCertListFieldsRep
    nm₁
  where
  nm₂ : NonMalleable (Raw&ₚ RawSignAlg (Raw×ₚ RawBitString RawOctetStringValue))
  nm₂ =
    Seq.nonmalleable
      {ra = RawSignAlg}
      {rb = Raw×ₚ RawBitString RawOctetStringValue}
      SignAlg.nonmalleable
      (Parallel.nonmalleable×ₚ{ra = RawBitString}{rb = RawOctetStringValue}
        BitString.nonmalleable
        OctetString.nonmalleableValue)

  nm₁ : NonMalleable RawCertListFieldsRep
  nm₁ =
    Seq.nonmalleable
      {ra = Raw×ₚ RawTBSCertList RawOctetStringValue}
      {rb = Raw&ₚ RawSignAlg (Raw×ₚ RawBitString RawOctetStringValue)}
      (Parallel.nonmalleable×ₚ TBSCertList.nonmalleable λ where self self refl → refl)
      nm₂

@0 nonmalleable : NonMalleable RawCertList
nonmalleable = TLV.nonmalleable{R = RawCertListFields} nonmalleableFields
