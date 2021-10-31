{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Prelude

module Aeres.Data.X509.Properties.UserNoticeFields where

open Base256
open import Aeres.Grammar.Definitions Dig

equivalent : Equivalent (&ₚ (Option X509.NoticeReference) (Option X509.DisplayText)) X509.UserNoticeFields
proj₂ equivalent (X509.mkUserNoticeFields noticeRef expText bs≡) = mk&ₚ noticeRef expText bs≡
proj₁ equivalent (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = X509.mkUserNoticeFields fstₚ₁ sndₚ₁ bs≡
