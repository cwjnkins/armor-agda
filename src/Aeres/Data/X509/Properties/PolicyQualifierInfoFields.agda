{-# OPTIONS --subtyping #-}


open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Prelude

module Aeres.Data.X509.Properties.PolicyQualifierInfoFields where

open Base256
open import Aeres.Grammar.Definitions Dig
open import Aeres.Grammar.Sum         Dig

module CPSURIQualifier where

  equivalent : Equivalent (&ₚ (_≡ X509.PQOID.CPSURI) X509.IA5String) X509.CPSURIQualifier
  proj₁ equivalent (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = X509.mkCPSURIQualifier fstₚ₁ sndₚ₁ bs≡
  proj₂ equivalent (X509.mkCPSURIQualifier ≡cpsuri cpsPointer bs≡) = mk&ₚ ≡cpsuri cpsPointer bs≡


module UserNoticeQualifier where

  equivalent : Equivalent (&ₚ (_≡ X509.PQOID.USERNOTICE) X509.UserNotice) X509.UserNoticeQualifier
  proj₁ equivalent (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = X509.mkUserNoticeQualifier fstₚ₁ sndₚ₁ bs≡
  proj₂ equivalent (X509.mkUserNoticeQualifier ≡usernotice unotice bs≡) = mk&ₚ ≡usernotice unotice bs≡


equivalent : Equivalent (Sum X509.CPSURIQualifier X509.UserNoticeQualifier) X509.PolicyQualifierInfoFields
proj₁ equivalent (Sum.inj₁ x) = X509.cpsURI x
proj₁ equivalent (Sum.inj₂ x) = X509.userNotice x
proj₂ equivalent (X509.cpsURI x) = Sum.inj₁ x
proj₂ equivalent (X509.userNotice x) = Sum.inj₂ x


postulate
  @0 nonnesting : NonNesting X509.PolicyQualifierInfoFields
-- nonnesting x (X509.cpsURI (X509.mkCPSURIQualifier refl (Generic.mkTLV len val len≡ refl) bs≡)) (X509.cpsURI (X509.mkCPSURIQualifier refl (Generic.mkTLV len₁ val₁ len≡₁ refl) bs≡₁)) = {!!}
-- nonnesting x (X509.cpsURI (X509.mkCPSURIQualifier refl (Generic.mkTLV len val len≡ refl) bs≡)) (X509.userNotice (X509.mkUserNoticeQualifier refl (Generic.mkTLV len₁ val₁ len≡₁ refl) bs≡₁)) = {!!}
-- nonnesting x (X509.userNotice (X509.mkUserNoticeQualifier refl (Generic.mkTLV len val len≡ bs≡₂) bs≡)) (X509.cpsURI (X509.mkCPSURIQualifier refl (Generic.mkTLV len₁ val₁ len≡₁ bs≡₃) bs≡₁)) = {!!}
-- nonnesting {xs₁}{ys₁}{xs₂}{ys₂} x (X509.userNotice (X509.mkUserNoticeQualifier refl (Generic.mkTLV{l}{v} len val len≡ refl) bs≡)) (X509.userNotice (X509.mkUserNoticeQualifier refl (Generic.mkTLV{l₁}{v₁} len₁ val₁ len≡₁ refl) bs≡₁)) = {!!}
