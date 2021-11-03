{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Decidable.Octetstring
open import Aeres.Data.X509.Decidable.Seq
open import Aeres.Data.X509.Decidable.TLV
open import Aeres.Data.X509.Decidable.UserNotice
open import Aeres.Data.X509.Properties as Props
open import Aeres.Grammar.Definitions
open import Aeres.Grammar.Parser
open import Data.List.Properties
open import Data.Nat.Properties
  hiding (_≟_)

module Aeres.Data.X509.Decidable.PolicyQualifierInfo where

open Base256

module parsePolicyQualifierInfo where
  here' = "parsePolicyQualifierInfo"

  parseCPSURIQualifier : Parser _ (Logging ∘ Dec) X509.CPSURIQualifier
  parseCPSURIQualifier =
    parseEquivalent _ Props.PolicyQualifierInfoFields.CPSURIQualifier.equivalent
      (parse& _ (λ where _ refl refl → refl)
        (parseLit _
          (tell $ here' String.++ ": CPS URI: underflow") (tell $ here' String.++ ": CPS URI: mismatch")
          X509.PQOID.CPSURI)
        parseIA5String)

  parseUserNoticeQualifier : Parser _ (Logging ∘ Dec) X509.UserNoticeQualifier
  parseUserNoticeQualifier =
    parseEquivalent _ Props.PolicyQualifierInfoFields.UserNoticeQualifier.equivalent
      (parse& _ (λ where _ refl refl → refl)
        (parseLit _
          (tell $ here' String.++ ": user notice: underflow") (tell $ here' String.++ ": user notice: mismatch")
          X509.PQOID.USERNOTICE)
        parseUserNotice)

  parsePolicyQualifierInfoFields : Parser _ (Logging ∘ Dec) X509.PolicyQualifierInfoFields
  parsePolicyQualifierInfoFields =
    parseEquivalent _ Props.PolicyQualifierInfoFields.equivalent
      (parseSum _ parseCPSURIQualifier parseUserNoticeQualifier)

  parsePolicyQualifierInfo : Parser _ (Logging ∘ Dec) X509.PolicyQualifierInfo
  parsePolicyQualifierInfo =
    parseTLV _ "policy qualifier info" _
      (parseExactLength _ Props.PolicyQualifierInfoFields.nonnesting
        (tell $ here' String.++ ": underflow")
        parsePolicyQualifierInfoFields)

  parsePolicyQualifiersSeq : Parser _ (Logging ∘ Dec) X509.PolicyQualifiersSeq
  parsePolicyQualifiersSeq =
    parseSeq "policy qualifier info" _ Props.TLV.nonempty Props.TLV.nonnesting
      parsePolicyQualifierInfo

open parsePolicyQualifierInfo public using (parsePolicyQualifierInfo ; parsePolicyQualifiersSeq)
