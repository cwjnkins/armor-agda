{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Decidable.Length
open import Aeres.Data.X509.Decidable.Octetstring
open import Aeres.Data.X509.Decidable.Seq
open import Aeres.Data.X509.Decidable.TLV
open import Aeres.Data.X509.Properties as Props
open import Aeres.Grammar.Definitions
open import Aeres.Grammar.Parser
open import Data.List.Properties
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Decidable.AIAFields where

open Base256

module parseAIAFields where
  here' = "parseAIAFields"

  open ≡-Reasoning

  postulate
    parseAccessMethod : Parser Dig (Logging ∘ Dec) X509.AccessMethod
    parseAccessDescFields : ∀ n → Parser Dig (Logging ∘ Dec) (ExactLength _ X509.AccessDescFields n)
    parseAIASeqElems : ∀ n → Parser Dig (Logging ∘ Dec) (ExactLength _ X509.AIASeqElems n)

  parseAccessDesc :  Parser Dig (Logging ∘ Dec) X509.AccessDesc
  parseAccessDesc = parseTLV _ "Access Description" _ parseAccessDescFields

 
  parseAIAFieldsSeq : Parser Dig (Logging ∘ Dec) X509.AIAFieldsSeq
  parseAIAFieldsSeq = parseTLV _ "AIA Seq Fields" _ parseAIASeqElems


  parseAIAFields : Parser Dig (Logging ∘ Dec) X509.AIAFields
  parseAIAFields = parseTLV _ "AIA Fields" _ (parseExactLength _ Props.TLV.nonnesting (tell $ here' String.++ ": underflow") parseAIAFieldsSeq)
