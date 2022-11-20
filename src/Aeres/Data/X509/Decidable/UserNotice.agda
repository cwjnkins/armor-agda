{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X509
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
      (parseOption₂ _ TLV.nonnesting DisplayText.nonnesting
        (DisplayText.noconfusionTLV (toWitnessFalse{Q = _ ∈? _} tt))
        parseNoticeReference parseDisplayText
        (tell $ here' String.++ ": underflow") n)

  parseUserNotice : Parser _ (Logging ∘ Dec) X509.UserNotice
  parseUserNotice =
    parseTLV _ "user notice" _ parseUserNoticeFields

open parseUserNotice public using (parseUserNotice)

-- private                         
--   module Test where

--   val₁ : List Dig
--   val₁ = # 48 ∷ # 4 ∷ # 22 ∷ # 2 ∷ # 65 ∷ [ # 66 ]

--   val₂ : List Dig
--   val₂ = # 48 ∷ # 18 ∷ # 48 ∷ # 12 ∷ # 22 ∷ # 2 ∷ # 67 ∷ # 68 ∷ # 48 ∷ # 6 ∷ # 2 ∷ # 1 ∷ # 1 ∷ # 2 ∷ # 1 ∷ # 2 ∷ # 22 ∷ # 2 ∷ # 65 ∷ [ # 66 ]

--   val₃ : List Dig
--   val₃ = # 48 ∷ # 14 ∷ # 48 ∷ # 12 ∷ # 22 ∷ # 2 ∷ # 67 ∷ # 68 ∷ # 48 ∷ # 6 ∷ # 2 ∷ # 1 ∷ # 1 ∷ # 2 ∷ # 1 ∷ [ # 2 ]

--   val₄ : List Dig
--   val₄ = # 48 ∷ [ # 0 ]

--   val₅ : List Dig
--   val₅ = # 48 ∷ # 18 ∷ # 22 ∷ # 2 ∷ # 65 ∷ # 66 ∷ # 48 ∷ # 12 ∷ # 22 ∷ # 2 ∷ # 67 ∷ # 68 ∷ # 48 ∷ # 6 ∷ # 2 ∷ # 1 ∷ # 1 ∷ # 2 ∷ # 1 ∷ [ # 2 ]

--   test₁ : X509.UserNotice val₁
--   test₁ = Success.value (toWitness {Q = Logging.val (runParser parseUserNotice val₁)} tt)

--   test₂ : X509.UserNotice val₂
--   test₂ = Success.value (toWitness {Q = Logging.val (runParser parseUserNotice val₂)} tt)

--   test₃ : X509.UserNotice val₃
--   test₃ = Success.value (toWitness {Q = Logging.val (runParser parseUserNotice val₃)} tt)

--   test₄ : X509.UserNotice val₄
--   test₄ = Success.value (toWitness {Q = Logging.val (runParser parseUserNotice val₄)} tt)

--   test₅ : ¬ Success _ X509.UserNotice val₅
--   test₅ = toWitnessFalse {Q = Logging.val (runParser parseUserNotice val₅)} tt
