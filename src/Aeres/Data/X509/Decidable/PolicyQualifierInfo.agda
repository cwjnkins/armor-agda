{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Decidable.Octetstring
open import Aeres.Data.X509.Decidable.UserNotice
open import Aeres.Data.X509.Properties as Props
open import Aeres.Grammar.Definitions
open import Aeres.Grammar.Parser
import      Aeres.Grammar.Sum
open import Data.List.Properties
open import Data.Nat.Properties
  hiding (_≟_)

module Aeres.Data.X509.Decidable.PolicyQualifierInfo where

open Aeres.Grammar.Sum UInt8
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
      (parseSum parseCPSURIQualifier parseUserNoticeQualifier)

  parsePolicyQualifierInfo : Parser _ (Logging ∘ Dec) X509.PolicyQualifierInfo
  parsePolicyQualifierInfo =
    parseTLV _ "policy qualifier info" _
      (parseExactLength _ Props.PolicyQualifierInfoFields.nonnesting
        (tell $ here' String.++ ": underflow")
        parsePolicyQualifierInfoFields)

  parsePolicyQualifiersSeq : Parser _ (Logging ∘ Dec) X509.PolicyQualifiersSeq
  parsePolicyQualifiersSeq =
    parseNonEmptySeq "policy qualifier info" _ TLV.nonempty TLV.nonnesting
      parsePolicyQualifierInfo

open parsePolicyQualifierInfo public using (parsePolicyQualifierInfo ; parsePolicyQualifiersSeq)


private
  module Test where

  val₁ : List Dig ---cps
  val₁ = # 48 ∷ # 42 ∷ # 48 ∷ # 40 ∷ # 6 ∷ # 8 ∷ # 43 ∷ # 6 ∷ # 1 ∷ # 5 ∷ # 5 ∷ # 7 ∷ # 2 ∷ # 1 ∷ # 22 ∷ # 28 ∷ # 104 ∷ # 116 ∷ # 116 ∷ # 112 ∷ # 115 ∷ # 58 ∷ # 47 ∷ # 47 ∷ # 119 ∷ # 119 ∷ # 119 ∷ # 46 ∷ # 100 ∷ # 105 ∷ # 103 ∷ # 105 ∷ # 99 ∷ # 101 ∷ # 114 ∷ # 116 ∷ # 46 ∷ # 99 ∷ # 111 ∷ # 109 ∷ # 47 ∷ # 67 ∷ # 80 ∷ [ # 83 ]

  val₂ : List Dig ---unotice
  val₂ =  # 48 ∷ # 32 ∷ # 48 ∷ # 30 ∷ # 6 ∷ # 8 ∷ # 43 ∷ # 6 ∷ # 1 ∷ # 5 ∷ # 5 ∷ # 7 ∷ # 2 ∷ # 2 ∷ # 48 ∷ # 18 ∷ # 48 ∷ # 12 ∷ # 22 ∷ # 2 ∷ # 67 ∷ # 68 ∷ # 48 ∷ # 6 ∷ # 2 ∷ # 1 ∷ # 1 ∷ # 2 ∷ # 1 ∷ # 2 ∷ # 22 ∷ # 2 ∷ # 65 ∷ [ # 66 ]

  test₁ : X509.PolicyQualifiersSeq val₁
  test₁ = Success.value (toWitness {Q = Logging.val (runParser parsePolicyQualifiersSeq val₁)} tt)

  test₂ : X509.PolicyQualifiersSeq val₂
  test₂ = Success.value (toWitness {Q = Logging.val (runParser parsePolicyQualifiersSeq val₂)} tt)
