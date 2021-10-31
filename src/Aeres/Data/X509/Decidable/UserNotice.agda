{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Decidable.TLV
open import Aeres.Data.X509.Decidable.NoticeReference
open import Aeres.Data.X509.Decidable.DisplayText
open import Aeres.Data.X509.Properties as Props
open import Aeres.Grammar.Definitions
open import Aeres.Grammar.Parser
open import Data.List.Properties
open import Data.Nat.Properties
  hiding (_≟_)

module Aeres.Data.X509.Decidable.UserNotice where

open Base256

module parseUserNotice where
  here' = "parseUserNotice"

  parseUserNoticeFields : ∀ n → Parser _ (Logging ∘ Dec) (ExactLength _ X509.UserNoticeFields n)
  parseUserNoticeFields n =
    parseEquivalent _ (equivalent×ₚ _ Props.UserNoticeFields.equivalent)
      (parseOption₂ _ Props.TLV.nonnesting Props.DisplayText.nonnesting Props.DisplayText.noconfusionNoticeReference
        parseNoticeReference parseDisplayText
        (tell $ here' String.++ ": underflow") n)

  parseUserNotice : Parser _ (Logging ∘ Dec) X509.UserNotice
  parseUserNotice =
    parseTLV _ "user notice" _ parseUserNoticeFields

open parseUserNotice using (parseUserNotice)
