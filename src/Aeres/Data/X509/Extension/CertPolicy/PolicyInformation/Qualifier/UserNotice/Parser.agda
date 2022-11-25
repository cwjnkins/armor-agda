{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.UserNotice.NoticeReference
open import Aeres.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.UserNotice.Properties
open import Aeres.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.UserNotice.TCB
open import Aeres.Data.X690-DER.SequenceOf.TCB
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Data.X509.DisplayText
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
import      Aeres.Grammar.Parser
import      Aeres.Grammar.Sum
open import Aeres.Prelude

module Aeres.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.UserNotice.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8
open Aeres.Grammar.Parser      UInt8
open Aeres.Grammar.Sum         UInt8

private
  here' = "X509: Extension: CertPolicy: PlicyInformation: Qualifier: UserNotice"

parseUserNoticeFields : ∀ n → Parser (Logging ∘ Dec) (ExactLength UserNoticeFields n)
parseUserNoticeFields n =
  parseEquivalent (equivalent×ₚ equivalent)
    (parseOption₂ TLV.nonnesting DisplayText.nonnesting
      (DisplayText.noconfusionTLV (toWitnessFalse{Q = _ ∈? _} tt))
      parseNoticeReference parseDisplayText
      (tell $ here' String.++ ": underflow") n)

parseUserNotice : Parser (Logging ∘ Dec) UserNotice
parseUserNotice =
  parseTLV _ "user notice" _ parseUserNoticeFields
