{-# OPTIONS --allow-unsolved-metas #-}
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

postulate
  @0 unambiguous : Unambiguous TBSCertList
  -- unambiguous = TLV.unambiguous (Iso.unambiguous iso ua₆)
  -- where

-- postulate
--   nc₁ : NoConfusion Time Rep₁
  -- nc₁ {xs₁} {ys₁} {xs₂} {ys₂} xs₁++ys₁≡xs₂++ys₂ (generalized a@(mkTLV len val len≡ bs≡₁)) b@(mk&ₚ none none refl) = 
  --   contradiction (∷-injectiveˡ (trans (cong (_++ ys₁) (sym bs≡₁)) {!!})) λ ()
  -- nc₁ {xs₁} {ys₁} {xs₂} {ys₂} xs₁++ys₁≡xs₂++ys₂ (generalized (mkTLV len val len≡ bs≡₁)) (mk&ₚ none (some (mkTLV len₁ val₁ len≡₁ bs≡₂)) bs≡) =
  --   contradiction (∷-injectiveˡ (trans (cong (_++ ys₁) (sym bs≡₁)) (trans xs₁++ys₁≡xs₂++ys₂ (cong (_++ ys₂) (trans bs≡ bs≡₂))))) λ ()
  -- nc₁ {xs₁} {ys₁} {xs₂} {ys₂} xs₁++ys₁≡xs₂++ys₂ (generalized (mkTLV len val len≡ bs≡₁)) (mk&ₚ (some (mkTLV len₁ val₁ len≡₁ refl)) none refl) =
  --   contradiction (∷-injectiveˡ (trans (cong (_++ ys₁) (sym bs≡₁)) (trans xs₁++ys₁≡xs₂++ys₂ (cong (_++ ys₂) refl)))) λ ()
  -- nc₁ {xs₁} {ys₁} {xs₂} {ys₂} xs₁++ys₁≡xs₂++ys₂ (generalized (mkTLV len val len≡ bs≡₁)) (mk&ₚ (some (mkTLV len₁ val₁ len≡₁ refl)) (some (mkTLV len₂ val₂ len≡₂ refl)) bs≡) =
  --   contradiction (∷-injectiveˡ (trans (cong (_++ ys₁) (sym bs≡₁)) (trans xs₁++ys₁≡xs₂++ys₂ (cong (_++ ys₂) bs≡)))) λ ()
  -- nc₁ {xs₁} {ys₁} {xs₂} {ys₂} xs₁++ys₁≡xs₂++ys₂ (utc (mkTLV len val len≡ bs≡₁)) (mk&ₚ none none refl) =
  --   contradiction (∷-injectiveˡ (trans (cong (_++ ys₁) (sym bs≡₁)) {!!})) λ ()
  -- nc₁ {xs₁} {ys₁} {xs₂} {ys₂} xs₁++ys₁≡xs₂++ys₂ (utc (mkTLV len val len≡ bs≡₁)) (mk&ₚ none (some (mkTLV len₁ val₁ len≡₁ bs≡₂)) bs≡) =
  --   contradiction (∷-injectiveˡ (trans (cong (_++ ys₁) (sym bs≡₁)) (trans xs₁++ys₁≡xs₂++ys₂ (cong (_++ ys₂) (trans bs≡ bs≡₂))))) λ ()
  -- nc₁ {xs₁} {ys₁} {xs₂} {ys₂} xs₁++ys₁≡xs₂++ys₂ (utc (mkTLV len val len≡ bs≡₁)) (mk&ₚ (some (mkTLV len₁ val₁ len≡₁ refl)) none refl) =
  --   contradiction (∷-injectiveˡ (trans (cong (_++ ys₁) (sym bs≡₁)) (trans xs₁++ys₁≡xs₂++ys₂ (cong (_++ ys₂) refl)))) λ ()
  -- nc₁ {xs₁} {ys₁} {xs₂} {ys₂} xs₁++ys₁≡xs₂++ys₂ (utc (mkTLV len val len≡ bs≡₁)) (mk&ₚ (some (mkTLV len₁ val₁ len≡₁ refl)) (some (mkTLV len₂ val₂ len≡₂ refl)) bs≡) =
  --   contradiction (∷-injectiveˡ (trans (cong (_++ ys₁) (sym bs≡₁)) (trans xs₁++ys₁≡xs₂++ys₂ (cong (_++ ys₂) bs≡)))) λ ()

  --   nc₂ : NoConfusion Version SignAlg
  -- -- nc₂ xs₁++ys₁≡xs₂++ys₂ (mk×ₚ v@(mkTLV len₁ val₁ len≡₁ bs≡) sndₚ₁) s@(mkTLV len val len≡ bs≡₁) =
  -- --   TLV.noconfusion (λ ()) xs₁++ys₁≡xs₂++ys₂ v s

  -- ns₁ : NoSubstrings Rep₅
  -- ns₁ = Seq.nosubstringsOption₁ Version.nosubstrings SignAlg.nosubstrings nc₂

  -- ua₁ : Unambiguous Rep₁
  -- ua₁ = Seq.unambiguousOption₂ RevokedCertificates.unambiguous TLV.nosubstrings TLV.nonempty Extension.unambiguous TLV.nonempty
  --   (TLV.noconfusion λ ())

  -- ua₂ : Unambiguous Rep₂
  -- ua₂ = Seq.unambiguousOption₁ Time.unambiguous Time.nosubstrings ua₁ nc₁

  -- ua₃ : Unambiguous Rep₃
  -- ua₃ = Seq.unambiguous Time.unambiguous Time.nosubstrings ua₂

  -- ua₄ : Unambiguous Rep₄
  -- ua₄ = Seq.unambiguous Name.unambiguous TLV.nosubstrings ua₃

  -- ua₅ : Unambiguous Rep₅
  -- ua₅ = ? -- Seq.unambiguousOption₁ Version.unambiguous Version.nosubstrings SignAlg.unambiguous nc₂

  -- ua₆ : Unambiguous Rep₆
  -- ua₆ = Seq.unambiguous ua₅ ns₁ ua₄

R₁ = Raw&ₚ (RawOption RawRevokedCertificates) (RawOption RawExtensions)
R₂ = Raw&ₚ (RawOption RawTime) R₁
R₃ = Raw&ₚ RawTime R₂
R₄ = Raw&ₚ RawName R₃
R₅ = Raw&ₚ (RawOption RawVersion) RawSignAlg
R₆ = Raw&ₚ R₅ R₄

@0 nonmalleableFields : NonMalleable RawTBSCertListFields
nonmalleableFields = Iso.nonmalleable iso RawTBSCertListFieldsRep nm₆
  where
  nm₁ : NonMalleable R₁
  nm₁ = Seq.nonmalleable{ra = RawOption RawRevokedCertificates}{rb = RawOption RawExtensions}
          (Option.nonmalleable _ RevokedCertificates.nonmalleable) (Option.nonmalleable _ Extension.nonmalleable)

  nm₂ : NonMalleable R₂
  nm₂ = Seq.nonmalleable{ra = RawOption RawTime}{rb = R₁} (Option.nonmalleable _ Time.nonmalleable) nm₁

  nm₃ : NonMalleable R₃
  nm₃ = Seq.nonmalleable{ra = RawTime}{rb = R₂} Time.nonmalleable nm₂

  nm₄ : NonMalleable R₄
  nm₄ = Seq.nonmalleable{ra = RawName}{rb = R₃} Name.nonmalleable nm₃

  nm₅ : NonMalleable R₅
  nm₅ = Seq.nonmalleable{ra = RawOption RawVersion}{rb = RawSignAlg} (Option.nonmalleable _ Version.nonmalleable) SignAlg.nonmalleable

  nm₆ : NonMalleable R₆
  nm₆ = Seq.nonmalleable{ra = R₅}{rb = R₄} nm₅ nm₄

@0 nonmalleable : NonMalleable RawTBSCertList
nonmalleable = TLV.nonmalleable nonmalleableFields
