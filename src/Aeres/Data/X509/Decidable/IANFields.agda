{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Decidable.GeneralName
open import Aeres.Data.X509.Decidable.Length
open import Aeres.Data.X509.Decidable.Seq
open import Aeres.Data.X509.Decidable.TLV
open import Aeres.Data.X509.Properties as Props
open import Aeres.Grammar.Definitions
open import Aeres.Grammar.Parser
open import Data.List.Properties
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Decidable.IANFields where

open Base256

module parseIANFields where
  here' = "parseIANFields"

  open ≡-Reasoning

  parseIANFields : Parser Dig (Logging ∘ Dec) X509.IANFields
  parseIANFields = parseTLV _ "IAN Fields" _ (parseExactLength _ Props.TLV.nonnesting (tell $ here' String.++ ": underflow") (parseSeq "IAN Fields Elems" _ Props.GeneralName.nonempty Props.GeneralName.nonnesting parseGeneralName))

open parseIANFields public using (parseIANFields)
