{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.UserNotice.NoticeReference
open import Aeres.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.UserNotice.TCB
open import Aeres.Data.X690-DER.SequenceOf.TCB
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Data.X509.DisplayText
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Sum
open import Aeres.Prelude

module Aeres.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.UserNotice.Properties where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8
open Aeres.Grammar.Properties  UInt8
open Aeres.Grammar.Sum         UInt8

Rep = &ₚ (Option NoticeReference) (Option DisplayText)

equivalent : Equivalent Rep UserNoticeFields
proj₂ equivalent (mkUserNoticeFields noticeRef expText bs≡) = mk&ₚ noticeRef expText bs≡
proj₁ equivalent (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = mkUserNoticeFields fstₚ₁ sndₚ₁ bs≡

iso : Iso Rep UserNoticeFields
proj₁ iso = equivalent
proj₁ (proj₂ iso) (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = refl
proj₂ (proj₂ iso) (mkUserNoticeFields noticeRef expText bs≡) = refl

private
  @0 nc : NoConfusion NoticeReference DisplayText
  nc = symNoConfusion{A = DisplayText}{B = NoticeReference}
         (NoConfusion.equivalent{A₁ = Sum _ _}{A₂ = DisplayText}{NoticeReference}
           DisplayText.equivalent
           (symNoConfusion{NoticeReference}{Sum _ _}
             (NoConfusion.sumₚ{NoticeReference}
               (NoConfusion.sigmaₚ₁ᵣ{A₁ = NoticeReference}
                 (TLV.noconfusion λ ()))
               (NoConfusion.sumₚ{NoticeReference}
                 (NoConfusion.sigmaₚ₁ᵣ{A₁ = NoticeReference} (TLV.noconfusion λ ()))
                 (NoConfusion.sumₚ{NoticeReference}
                   (NoConfusion.sigmaₚ₁ᵣ{A₁ = NoticeReference} (TLV.noconfusion λ ()))
                   (NoConfusion.sigmaₚ₁ᵣ{A₁ = NoticeReference} (TLV.noconfusion λ ())))))))

@0 unambiguous : Unambiguous UserNoticeFields
unambiguous =
  Iso.unambiguous iso
    (Unambiguous.option₂&₁
      (TLV.unambiguous NoticeReference.unambiguous) TLV.nonnesting TLV.nonempty
      DisplayText.unambiguous DisplayText.nonempty
      nc)
