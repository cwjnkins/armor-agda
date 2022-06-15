{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Decidable.GeneralName
open import Aeres.Data.X509.Properties as Props
open import Aeres.Grammar.Definitions
open import Aeres.Grammar.Parser
open import Data.List.Properties
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Decidable.NCFields where

open Base256
open import Aeres.Grammar.Properties  Dig

module parseNCFields where
  here' = "parseNCFields"

  open ≡-Reasoning

  parseExactLengthGeneralSubtrees : (n : ℕ) → Parser Dig (Logging ∘ Dec) (ExactLength Dig (X509.GeneralSubtrees) n)
  parseExactLengthGeneralSubtrees =
    parseExactLength _ TLV.nonnesting (tell $ here' String.++ ": underflow")
      (parseNonEmptySeq "GeneralSubtrees" _ TLV.nonempty TLV.nonnesting
        (parseTLV _ "GeneralSubtrees" _ helper))
    where
    helper : (n : ℕ) → Parser Dig (Logging ∘ Dec) (ExactLength Dig (X509.GeneralSubtreeFields) n)
    helper n =
      parseEquivalent _ (transEquivalent _ (symEquivalent _ Distribute.exactLength-&) (equivalent×ₚ _ Props.GeneralSubtreeFields.equivalent))
        (parse&ᵈ _ (withinLength-nonnesting _ Props.GeneralName.nonnesting)
          (withinLength-unambiguous _ Props.GeneralName.unambiguous)
          (parse≤ _ n parseGeneralName Props.GeneralName.nonnesting (tell $ here' String.++ ": underflow"))
          λ where
            {bs} (singleton read read≡) _ →
              subst₀ (λ x → Parser _ (Logging ∘ Dec) (ExactLength _ _ (n - x))) read≡
              (parseOption₂ _ TLV.nonnesting TLV.nonnesting (TLV.noconfusion λ ())
                (parseTLV _ "MinBaseDistance" _ parseIntValue)
                (parseTLV _ "MaxBaseDistance" _ parseIntValue)
                (tell $ here' String.++ ": underflow")
                (n - read)))

  parseNCFields : Parser Dig (Logging ∘ Dec) X509.NCFields
  parseNCFields =
    parseTLV _ "NC Fields" _
      (parseExactLength _ TLV.nonnesting (tell $ here' String.++ ": underflow")
        (parseTLV _ "NC Fields" _ helper))
    where
    helper : (n : ℕ) → Parser Dig (Logging ∘ Dec) (ExactLength Dig (X509.NCFieldsSeqFields) n)
    helper n =
      parseEquivalent _ (equivalent×ₚ _ Props.NCFieldsSeqFields.equivalent)
        (parseOption₂ _ TLV.nonnesting TLV.nonnesting (TLV.noconfusion λ ())
          (parseTLV _ "GeneralSubtrees" _ parseExactLengthGeneralSubtrees)
          (parseTLV _ "GeneralSubtrees" _ parseExactLengthGeneralSubtrees)
            (tell $ here' String.++ ": underflow") n)

open parseNCFields public using (parseNCFields)
