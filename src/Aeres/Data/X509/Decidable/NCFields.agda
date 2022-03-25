{-# OPTIONS --subtyping --allow-unsolved-metas #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Decidable.GeneralName
open import Aeres.Data.X509.Decidable.Int
open import Aeres.Data.X509.Decidable.Length
open import Aeres.Data.X509.Decidable.SequenceOf
open import Aeres.Data.X509.Decidable.TLV
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
    parseExactLength _ Props.TLV.nonnesting (tell $ here' String.++ ": underflow")
      (parseNonEmptySeq "aaa" _ Props.TLV.nonempty Props.TLV.nonnesting
        (parseTLV _ "aaa" _ {!!}))
    where
    helper : (n : ℕ) → Parser Dig (Logging ∘ Dec) (ExactLength Dig (X509.GeneralSubtreeFields) n)
    helper n = {!parse&ᵈ!}


  parseNCFields : Parser Dig (Logging ∘ Dec) X509.NCFields
  parseNCFields =
    parseTLV _ "aaa" _
      (parseExactLength _ Props.TLV.nonnesting (tell $ here' String.++ ": underflow")
        (parseTLV _ "aaa" _ helper))
    where
    helper : (n : ℕ) → Parser Dig (Logging ∘ Dec) (ExactLength Dig (X509.NCFieldsSeqFields) n)
    helper n =
      parseEquivalent _ (equivalent×ₚ _ Props.NCFieldsSeqFields.equivalent)
        (parseOption₂ _ Props.TLV.nonnesting Props.TLV.nonnesting (Props.TLV.noconfusion λ ())
          (parseTLV _ "aaa" _ parseExactLengthGeneralSubtrees)
          (parseTLV _ "aaa" _ parseExactLengthGeneralSubtrees)
            (tell $ here' String.++ ": underflow") n)

open parseNCFields public using (parseNCFields)




  -- parsePolicyMapFields : Parser _ (Logging ∘ Dec) X509.PolicyMapFields
  -- parsePolicyMapFields =
  --   parseEquivalent _ Props.PolicyMapFields.equivalent
  --     (parse& _ Props.TLV.nonnesting parseOID parseOID)

  -- parsePMFields : Parser Dig (Logging ∘ Dec) X509.PMFields
  -- parsePMFields =
  --   parseTLV _ "Policy Mappings" _
  --     (parseExactLength _  Props.TLV.nonnesting (tell $ here' String.++ ": underflow")
  --       (parseNonEmptySeq "Policy Mappings elems" _ Props.TLV.nonempty Props.TLV.nonnesting
  --         (parseTLV _ "aaa" _
  --           (λ n → parseExactLength _ Props.PolicyMapFields.nonnesting (tell $ here' String.++ ": underflow") parsePolicyMapFields n))))
