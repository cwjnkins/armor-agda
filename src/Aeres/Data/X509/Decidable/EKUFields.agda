{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Decidable.Length
open import Aeres.Data.X509.Decidable.OID
open import Aeres.Data.X509.Decidable.Seq
open import Aeres.Data.X509.Decidable.TLV
open import Aeres.Data.X509.Properties as Props
open import Aeres.Grammar.Definitions
open import Aeres.Grammar.Parser
open import Data.List.Properties
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Decidable.EKUFields where

open Base256

module parseEKUFields where
  here' = "parseEKUFields"

  open ≡-Reasoning

  parseEKUFields : Parser Dig (Logging ∘ Dec) X509.EKUFields
  parseEKUFields = parseTLV _ "EKU Fields" _ (parseExactLength _ Props.TLV.nonnesting (tell $ here' String.++ ": underflow") (parseSeq "EKU Fields Elems" _ Props.TLV.nonempty Props.TLV.nonnesting parseOID))

open parseEKUFields public using (parseEKUFields)

private
  module Test where

    val₁ : List Dig
    val₁ = # 4 ∷ # 12 ∷ # 48 ∷ # 10 ∷ # 6 ∷ # 8 ∷ # 43 ∷ # 6 ∷ # 1 ∷ # 5 ∷ # 5 ∷ # 7 ∷ # 3 ∷ [ # 1 ]

    val₂ : List Dig
    val₂ = # 4 ∷ # 22 ∷ # 48 ∷ # 20 ∷ # 6 ∷ # 8 ∷ # 43 ∷ # 6 ∷ # 1 ∷ # 5 ∷ # 5 ∷ # 7 ∷ # 3 ∷ # 1 ∷ # 6 ∷ # 8 ∷ # 43 ∷ # 6 ∷ # 1 ∷ # 5 ∷ # 5 ∷ # 7 ∷ # 3 ∷ [ # 2 ]

    test₁ : X509.EKUFields val₁
    test₁ = Success.value (toWitness {Q = Logging.val (runParser parseEKUFields val₁)} tt)

    test₂ : X509.EKUFields val₂
    test₂ = Success.value (toWitness {Q = Logging.val (runParser parseEKUFields val₂)} tt)
