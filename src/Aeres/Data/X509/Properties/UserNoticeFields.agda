{-# OPTIONS --subtyping #-}

open import Aeres.Binary
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Sum
open import Aeres.Data.X509
import      Aeres.Data.X509.Properties.DisplayText as DisplayTextProps
import      Aeres.Data.X509.Properties.NoticeReferenceFields as NRFProps
open import Aeres.Data.X690-DER
open import Aeres.Prelude

module Aeres.Data.X509.Properties.UserNoticeFields where

open Base256
open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8
open Aeres.Grammar.Properties  UInt8
open Aeres.Grammar.Sum         UInt8

equivalent : Equivalent (&ₚ (Option X509.NoticeReference) (Option X509.DisplayText)) X509.UserNoticeFields
proj₂ equivalent (X509.mkUserNoticeFields noticeRef expText bs≡) = mk&ₚ noticeRef expText bs≡
proj₁ equivalent (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = X509.mkUserNoticeFields fstₚ₁ sndₚ₁ bs≡

iso : Iso (&ₚ (Option X509.NoticeReference) (Option X509.DisplayText)) X509.UserNoticeFields
proj₁ iso = equivalent
proj₁ (proj₂ iso) (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = refl
proj₂ (proj₂ iso) (X509.mkUserNoticeFields noticeRef expText bs≡) = refl

private
  @0 nc : NoConfusion X509.NoticeReference X509.DisplayText
  nc = symNoConfusion{A = X509.DisplayText}{B = X509.NoticeReference}
         (NoConfusion.equivalent{A₁ = Sum _ _}{A₂ = X509.DisplayText}{X509.NoticeReference}
           DisplayTextProps.equivalent
           (symNoConfusion{X509.NoticeReference}{Sum _ _}
             (NoConfusion.sumₚ{X509.NoticeReference}
               (NoConfusion.sigmaₚ₁ᵣ{A₁ = X509.NoticeReference}
                 (TLV.noconfusion λ ()))
               (NoConfusion.sumₚ{X509.NoticeReference}
                 (NoConfusion.sigmaₚ₁ᵣ{A₁ = X509.NoticeReference} (TLV.noconfusion λ ()))
                 (NoConfusion.sumₚ{X509.NoticeReference}
                   (NoConfusion.sigmaₚ₁ᵣ{A₁ = X509.NoticeReference} (TLV.noconfusion λ ()))
                   (NoConfusion.sigmaₚ₁ᵣ{A₁ = X509.NoticeReference} (TLV.noconfusion λ ())))))))

@0 unambiguous : Unambiguous X509.UserNoticeFields
unambiguous =
  isoUnambiguous iso
    (Unambiguous.option₂&₁
      (TLV.unambiguous NRFProps.unambiguous) TLV.nonnesting TLV.nonempty
      DisplayTextProps.unambiguous DisplayTextProps.nonempty
      nc)
