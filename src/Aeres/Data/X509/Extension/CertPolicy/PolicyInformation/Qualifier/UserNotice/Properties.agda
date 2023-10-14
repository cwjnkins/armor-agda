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
import      Aeres.Grammar.Seq
import      Aeres.Grammar.Sum
open import Aeres.Prelude

module Aeres.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.UserNotice.Properties where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8
open Aeres.Grammar.Properties  UInt8
open Aeres.Grammar.Seq         UInt8
open Aeres.Grammar.Sum         UInt8

iso : Iso UserNoticeFieldsRep UserNoticeFields
proj₁ iso = equivalentUserNoticeFields
proj₁ (proj₂ iso) (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = refl
proj₂ (proj₂ iso) (mkUserNoticeFields noticeRef expText bs≡) = refl

private
  @0 nc : NoConfusion NoticeReference DisplayText
  nc = symNoConfusion{A = DisplayText}{B = NoticeReference}
         (NoConfusion.equivalent{A₁ = Sum _ _}{A₂ = DisplayText}{NoticeReference}
           DisplayText.equivalent
           (symNoConfusion{NoticeReference}{Sum _ _}
             (Sum.noconfusion{NoticeReference}
               (NoConfusion.sigmaₚ₁ᵣ{A₁ = NoticeReference}
                 (TLV.noconfusion λ ()))
               (Sum.noconfusion{NoticeReference}
                 (NoConfusion.sigmaₚ₁ᵣ{A₁ = NoticeReference} (TLV.noconfusion λ ()))
                 (Sum.noconfusion{NoticeReference}
                   (NoConfusion.sigmaₚ₁ᵣ{A₁ = NoticeReference} (TLV.noconfusion λ ()))
                   (NoConfusion.sigmaₚ₁ᵣ{A₁ = NoticeReference} (TLV.noconfusion λ ())))))))

@0 unambiguous : Unambiguous UserNotice
unambiguous =
  TLV.unambiguous (Iso.unambiguous iso
    (Unambiguous.option₂&₁
      (NoticeReference.unambiguous) TLV.nosubstrings TLV.nonempty
      DisplayText.unambiguous DisplayText.nonempty
      nc))

@0 nonmalleable : NonMalleable RawUserNotice
nonmalleable = TLV.nonmalleable
                 (Iso.nonmalleable iso RawUserNoticeFieldsRep
                   (Seq.nonmalleable (Option.nonmalleable _ NoticeReference.nonmalleable)
                     (Option.nonmalleable _ DisplayText.nonmalleable)))
