{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Decidable.DistPoint
open import Aeres.Data.X509.Properties as Props
open import Aeres.Grammar.Definitions
open import Aeres.Grammar.Parser
open import Data.List.Properties
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Decidable.CRLDistFields where

open Base256

module parseCRLDistFields where
  here' = "parseCRLDistFields"

  open ≡-Reasoning

  parseCRLDistFields : Parser Dig (Logging ∘ Dec) X509.CRLDistFields
  parseCRLDistFields =
    parseTLV _ "CRL Dist Fields" _
      (parseExactLength _ TLV.nonnesting (tell $ here' String.++ ": underflow")
        (parseNonEmptySeq "CRL Dist fields elems" _ TLV.nonempty TLV.nonnesting
          parseDistPoint))


open parseCRLDistFields public using (parseCRLDistFields)
