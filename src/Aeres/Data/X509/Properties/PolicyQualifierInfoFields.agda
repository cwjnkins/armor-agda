{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Prelude

module Aeres.Data.X509.Properties.PolicyQualifierInfoFields where

open Base256
open import Aeres.Grammar.Definitions Dig
open import Aeres.Grammar.Sum         Dig

module CPSURIQualifier where
  postulate
    equivalent : Equivalent (&ₚ (_≡ X509.PQOID.CPSURI) X509.IA5String) X509.CPSURIQualifier

module UserNoticeQualifier where
  postulate
    equivalent : Equivalent (&ₚ (_≡ X509.PQOID.USERNOTICE) X509.UserNotice) X509.UserNoticeQualifier

postulate
  equivalent : Equivalent (Sum X509.CPSURIQualifier X509.UserNoticeQualifier) X509.PolicyQualifierInfoFields
