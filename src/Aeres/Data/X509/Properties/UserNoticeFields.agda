{-# OPTIONS --subtyping #-}

open import Aeres.Binary
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Sum
open import Aeres.Data.X509
import      Aeres.Data.X509.Properties.DisplayText as DisplayTextProps
import      Aeres.Data.X509.Properties.NoticeReferenceFields as NRFProps
import      Aeres.Data.X509.Properties.TLV         as TLVProps
open import Aeres.Prelude

module Aeres.Data.X509.Properties.UserNoticeFields where

open Base256
open Aeres.Grammar.Definitions Dig
open Aeres.Grammar.Properties  Dig
open Aeres.Grammar.Sum         Dig

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
               (TLVProps.noconfusion (λ ()))
               (NoConfusion.sumₚ{X509.NoticeReference}
                 (TLVProps.noconfusion λ ())
                 (NoConfusion.sumₚ{X509.NoticeReference}
                   (TLVProps.noconfusion λ ()) (TLVProps.noconfusion λ ()))))))

@0 unambiguous : Unambiguous X509.UserNoticeFields
unambiguous =
  isoUnambiguous iso
    (Unambiguous.option₂&₁
      (TLVProps.unambiguous NRFProps.unambiguous) TLVProps.nonnesting TLVProps.nonempty
      DisplayTextProps.unambiguous DisplayTextProps.nonempty
      nc)
