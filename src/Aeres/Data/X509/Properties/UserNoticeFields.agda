{-# OPTIONS --subtyping #-}

open import Aeres.Binary
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Sum
open import Aeres.Data.X509
open import Aeres.Data.X690-DER
open import Aeres.Prelude

module Aeres.Data.X509.Properties.UserNoticeFields where

open Base256
open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8
open Aeres.Grammar.Properties  UInt8
open Aeres.Grammar.Sum         UInt8

equivalent : Equivalent (&ₚ (Option NoticeReference) (Option DisplayText)) X509.UserNoticeFields
proj₂ equivalent (X509.mkUserNoticeFields noticeRef expText bs≡) = mk&ₚ noticeRef expText bs≡
proj₁ equivalent (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = X509.mkUserNoticeFields fstₚ₁ sndₚ₁ bs≡

iso : Iso (&ₚ (Option NoticeReference) (Option DisplayText)) X509.UserNoticeFields
proj₁ iso = equivalent
proj₁ (proj₂ iso) (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = refl
proj₂ (proj₂ iso) (X509.mkUserNoticeFields noticeRef expText bs≡) = refl

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

@0 unambiguous : Unambiguous X509.UserNoticeFields
unambiguous =
  isoUnambiguous iso
    (Unambiguous.option₂&₁
      (TLV.unambiguous NoticeReference.unambiguous) TLV.nonnesting TLV.nonempty
      DisplayText.unambiguous DisplayText.nonempty
      nc)
