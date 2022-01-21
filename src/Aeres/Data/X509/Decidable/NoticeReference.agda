{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Decidable.DisplayText
open import Aeres.Data.X509.Decidable.SequenceOf
open import Aeres.Data.X509.Decidable.TLV
open import Aeres.Data.X509.Properties as Props
open import Aeres.Grammar.Definitions
open import Aeres.Grammar.Parser
open import Data.List.Properties
open import Data.Nat.Properties
  hiding (_≟_)
-- open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Decidable.NoticeReference where

open Base256

module parseNoticeReference where
  here' = "parseNoticeReference"

  open ≡-Reasoning

  parseNoticeReferenceFields : ∀ n → Parser Dig (Logging ∘ Dec) (ExactLength _ X509.NoticeReferenceFields n)
  runParser (parseNoticeReferenceFields n) xs = do
    yes x ←
      runParser (parseExactLength _ (NonNesting&ₚ _ Props.DisplayText.nonnesting Props.TLV.nonnesting)
                  (tell $ here' String.++ ": underflow")
                  (parse& _ Props.DisplayText.nonnesting parseDisplayText parseIntegerSeq) n)
                xs
      where no ¬parse → do
        return ∘ no $ λ where
          (success prefix read read≡ (mk×ₚ (X509.mkNoticeReferenceFields organiztion noticenums bs≡₁) sndₚ₁ bs≡) suffix ps≡) →
            contradiction
              (success prefix _ read≡ (mk×ₚ (mk&ₚ organiztion noticenums bs≡₁) sndₚ₁ bs≡) suffix ps≡)
              ¬parse
    return (yes
      (mapSuccess _
        (λ where
          {xs} (mk×ₚ (mk&ₚ orgs notices bs≡₁) vLen bs≡) →
            mk×ₚ (X509.mkNoticeReferenceFields orgs notices bs≡₁) vLen bs≡)
        x))

  parseNoticeReference : Parser Dig (Logging ∘ Dec) X509.NoticeReference
  parseNoticeReference = parseTLV _ "notice reference: " _ parseNoticeReferenceFields

open parseNoticeReference public using (parseNoticeReferenceFields ; parseNoticeReference)


private                         
  module Test where

  val₁ : List Dig
  val₁ = # 48 ∷ # 12 ∷ # 22 ∷ # 2 ∷ # 67 ∷ # 68 ∷ # 48 ∷ # 6 ∷ # 2 ∷ # 1 ∷ # 1 ∷ # 2 ∷ # 1 ∷ [ # 2 ]

  test₁ : X509.NoticeReference val₁
  test₁ = Success.value (toWitness {Q = Logging.val (runParser parseNoticeReference val₁)} tt)
