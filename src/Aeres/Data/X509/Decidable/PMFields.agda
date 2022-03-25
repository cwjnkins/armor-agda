{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Decidable.GeneralName
open import Aeres.Data.X509.Decidable.Int
open import Aeres.Data.X509.Decidable.Length
open import Aeres.Data.X509.Decidable.OID
open import Aeres.Data.X509.Decidable.SequenceOf
open import Aeres.Data.X509.Decidable.TLV
open import Aeres.Data.X509.Properties as Props
open import Aeres.Grammar.Definitions
open import Aeres.Grammar.Parser
open import Data.List.Properties
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Decidable.PMFields where

open Base256

module parsePMFields where
  here' = "parsePMFields"

  open ≡-Reasoning


  parsePolicyMapFields : Parser _ (Logging ∘ Dec) X509.PolicyMapFields
  parsePolicyMapFields =
    parseEquivalent _ Props.PolicyMapFields.equivalent
      (parse& _ Props.TLV.nonnesting parseOID parseOID)

  parsePMFields : Parser Dig (Logging ∘ Dec) X509.PMFields
  parsePMFields =
    parseTLV _ "Policy Mappings" _
      (parseExactLength _  Props.TLV.nonnesting (tell $ here' String.++ ": underflow")
        (parseNonEmptySeq "Policy Mappings elems" _ Props.TLV.nonempty Props.TLV.nonnesting
          (parseTLV _ "aaa" _
            (λ n → parseExactLength _ Props.PolicyMapFields.nonnesting (tell $ here' String.++ ": underflow") parsePolicyMapFields n))))


open parsePMFields public using (parsePMFields)
