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
proj₁ (proj₂ iso) (mk&ₚ (mk&ₚ fstₚ₁ sndₚ₂ refl) sndₚ₁ bs≡) =  subst₀ (λ eq → mk&ₚ _ _ eq ≡ mk&ₚ _ _ bs≡) (≡-unique bs≡ (trans₀ (trans₀ bs≡ _) _)) refl
proj₂ (proj₂ iso) (mkCertListFields tbs signAlg signature bs≡) =
  subst₀ (λ eq → mkCertListFields tbs signAlg signature eq
     ≡ mkCertListFields _ _ _ bs≡) (≡-unique bs≡ _) refl

@0 unambiguous : Unambiguous CertList
unambiguous = TLV.unambiguous (Iso.unambiguous iso
  (Seq.unambiguous (Seq.unambiguous TBSCertList.unambiguous TLV.nosubstrings SignAlg.unambiguous)
    (Seq.nosubstrings TLV.nosubstrings TLV.nosubstrings) BitString.unambiguous))

@0 nonmalleableFields : NonMalleable RawCertListFields
nonmalleableFields = Iso.nonmalleable iso RawCertListFieldsRep nm₁
  where
  nm₂ : NonMalleable (Raw&ₚ RawTBSCertList RawSignAlg)
  nm₂ = Seq.nonmalleable{ra = RawTBSCertList}{rb = RawSignAlg} TBSCertList.nonmalleable SignAlg.nonmalleable

  nm₁ : NonMalleable RawCertListFieldsRep
  nm₁ = Seq.nonmalleable{ra = Raw&ₚ RawTBSCertList RawSignAlg}{rb = RawBitString}
        nm₂ BitString.nonmalleable

@0 nonmalleable : NonMalleable RawCertList
nonmalleable = TLV.nonmalleable nonmalleableFields
