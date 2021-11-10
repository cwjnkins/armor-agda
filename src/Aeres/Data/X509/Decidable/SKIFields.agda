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

module Aeres.Data.X509.Decidable.SKIFields where

open Base256

module parseSKIFields where
  here' = "parseSKIFields"

  open ≡-Reasoning

  parseSKIFields : Parser Dig (Logging ∘ Dec) X509.SKIFields
  parseSKIFields = parseTLV _ "SKI Fields" _ (parseExactLength _ Props.TLV.nonnesting (tell $ here' String.++ ": underflow") parseOctetstring )

open parseSKIFields public using (parseSKIFields)


private
  module Test where

    val₁ : List Dig
    val₁ = # 4 ∷ # 22 ∷ # 4 ∷ # 20 ∷ # 147 ∷ # 61 ∷ # 128 ∷ # 160 ∷ # 120 ∷ # 95 ∷ # 164 ∷ # 18 ∷ # 101 ∷ # 194 ∷ # 57 ∷ # 173 ∷ # 54 ∷ # 77 ∷ # 116 ∷ # 177 ∷ # 171 ∷ # 84 ∷ # 108 ∷ [ # 167 ]

    test₁ : X509.SKIFields val₁
    test₁ = Success.value (toWitness {Q = Logging.val (runParser parseSKIFields val₁)} tt)
