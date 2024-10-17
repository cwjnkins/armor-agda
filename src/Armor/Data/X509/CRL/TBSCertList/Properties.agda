open import Armor.Binary
open import Armor.Data.X690-DER.TLV
open import Armor.Data.X509.CRL.TBSCertList.TCB
open import Armor.Data.X509.CRL.Version
open import Armor.Data.X509.CRL.Extension
open import Armor.Data.X509.CRL.RevokedCertificates
open import Armor.Data.X509.SignAlg
open import Armor.Data.X509.Name
open import Armor.Data.X690-DER.Int
open import Armor.Data.X509.Validity.Time
import      Armor.Data.X690-DER.Tag as Tag
open import Armor.Data.X690-DER.SequenceOf
import      Armor.Grammar.IList.TCB
import      Armor.Grammar.Sum
import      Armor.Grammar.Option
import      Armor.Grammar.Definitions
import      Armor.Grammar.Seq
import      Armor.Grammar.Parallel
open import Armor.Prelude

module Armor.Data.X509.CRL.TBSCertList.Properties where

open Armor.Grammar.Seq    UInt8
open Armor.Grammar.Sum    UInt8
open Armor.Grammar.Parallel    UInt8
open Armor.Grammar.IList.TCB    UInt8
open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8

iso : Iso TBSCertListFieldsRep TBSCertListFields
proj₁ iso = equivalentTBSCertListFields
proj₁ (proj₂ iso) (mk&ₚ(mk&ₚ version signAlg refl)
      (mk&ₚ issuer
        (mk&ₚ thisUpdate
          (mk&ₚ nextUpdate
            (mk&ₚ revokedCertificates crlExtensions refl) refl) refl) refl) bs≡)
      = subst₀ (λ eq → mk&ₚ _ _ eq ≡ mk&ₚ _ _ bs≡) (≡-unique bs≡ (trans₀ (trans₀ bs≡ _) _)) refl
proj₂ (proj₂ iso) (mkTBSCertListFields version signAlg issuer thisUpdate nextUpdate revokedCertificates crlExtensions bs≡)
   = subst₀ (λ eq → mkTBSCertListFields version signAlg issuer thisUpdate nextUpdate revokedCertificates crlExtensions eq
     ≡ mkTBSCertListFields _ _ _ _ _ _ _ bs≡) (≡-unique bs≡ _) refl

@0 ncVersionSignAlg : NoConfusion Version SignAlg
ncVersionSignAlg xs₁++ys₁≡xs₂++ys₂ (mk×ₚ v@(mkTLV len₁ val₁ len≡₁ bs≡) sndₚ₁) s@(mkTLV len val len≡ bs≡₁) =
    TLV.noconfusion (λ ()) xs₁++ys₁≡xs₂++ys₂ v s

@0 ncTimeRevokedCertificates : NoConfusion Time RevokedCertificates
ncTimeRevokedCertificates xs₁++ys₁≡xs₂++ys₂ (generalized x₁) x = TLV.noconfusion (λ ()) xs₁++ys₁≡xs₂++ys₂ x₁ x
ncTimeRevokedCertificates xs₁++ys₁≡xs₂++ys₂ (utc x₁) x = TLV.noconfusion (λ ()) xs₁++ys₁≡xs₂++ys₂ x₁ x

@0 ncTimeExtensions : NoConfusion Time Extensions
ncTimeExtensions xs₁++ys₁≡xs₂++ys₂ (generalized x₁) x = TLV.noconfusion (λ ()) xs₁++ys₁≡xs₂++ys₂ x₁ x
ncTimeExtensions xs₁++ys₁≡xs₂++ys₂ (utc x₁) x = TLV.noconfusion (λ ()) xs₁++ys₁≡xs₂++ys₂ x₁ x

@0 nsRep₅ : NoSubstrings Rep₅
nsRep₅ = Seq.nosubstringsOption₁{A = Version}{B = SignAlg} Version.nosubstrings SignAlg.nosubstrings ncVersionSignAlg

@0 unambiguous : Unambiguous TBSCertList
unambiguous = TLV.unambiguous (Iso.unambiguous iso ua₆)
  where
  ua₂ : Unambiguous Rep₂
  ua₂ = Seq.unambiguous₂Option₃ Time.unambiguous Time.nosubstrings Time.nonempty
    RevokedCertificates.unambiguous TLV.nosubstrings TLV.nonempty Extension.unambiguous
    TLV.nonempty ncTimeRevokedCertificates ncTimeExtensions (TLV.noconfusion (λ ()))

  ua₃ : Unambiguous Rep₃
  ua₃ = Seq.unambiguous Time.unambiguous Time.nosubstrings ua₂ 

  ua₄ : Unambiguous Rep₄
  ua₄ = Seq.unambiguous Name.unambiguous TLV.nosubstrings ua₃

  ua₅ : Unambiguous Rep₅
  ua₅ = Seq.unambiguousOption₁ Version.unambiguous Version.nosubstrings SignAlg.unambiguous ncVersionSignAlg

  ua₆ : Unambiguous Rep₆
  ua₆ = Seq.unambiguous ua₅ nsRep₅ ua₄

@0 nonmalleable : NonMalleable RawTBSCertList
nonmalleable = TLV.nonmalleable (Iso.nonmalleable iso RawTBSCertListFieldsRep nm₆)
  where
  R = Raw&ₚ (RawOption RawRevokedCertificates) (RawOption RawExtensions)
  R₁ = Raw&ₚ (RawOption RawTime) R
  R₂ = Raw&ₚ RawTime R₁
  R₃ = Raw&ₚ RawName R₂
  R₄ = Raw&ₚ (RawOption RawVersion) RawSignAlg
  R₅ = Raw&ₚ R₄ R₃

  nm₁ : NonMalleable R
  nm₁ = Seq.nonmalleable{ra = RawOption RawRevokedCertificates}{rb = RawOption RawExtensions}
          (Option.nonmalleable _ RevokedCertificates.nonmalleable) (Option.nonmalleable _ Extension.nonmalleable)

  nm₂ : NonMalleable R₁
  nm₂ = Seq.nonmalleable{ra = RawOption RawTime}{rb = R} (Option.nonmalleable _ Time.nonmalleable) nm₁

  nm₃ : NonMalleable R₂
  nm₃ = Seq.nonmalleable{ra = RawTime}{rb = R₁} Time.nonmalleable nm₂

  nm₄ : NonMalleable R₃
  nm₄ = Seq.nonmalleable{ra = RawName}{rb = R₂} Name.nonmalleable nm₃

  nm₅ : NonMalleable R₄
  nm₅ = Seq.nonmalleable{ra = RawOption RawVersion}{rb = RawSignAlg} (Option.nonmalleable _ Version.nonmalleable) SignAlg.nonmalleable

  nm₆ : NonMalleable R₅
  nm₆ = Seq.nonmalleable{ra = R₄}{rb = R₃} nm₅ nm₄
