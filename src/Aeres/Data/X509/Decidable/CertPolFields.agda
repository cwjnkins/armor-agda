{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Properties as Props
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
import      Aeres.Grammar.Parser
open import Data.List.Properties
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Decidable.CertPolFields where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8
open Aeres.Grammar.Parser      UInt8

module parseCertPolFields where
  here' = "parseCertPolFields"

  open ≡-Reasoning

  parseCertPolFieldsSeq : Parser (Logging ∘ Dec) X509.CertPolFieldsSeq
  parseCertPolFieldsSeq = parseNonEmptySeq "policy info" _ TLV.nonempty TLV.nonnesting parsePolicyInformation

  parseCertPolFields : Parser (Logging ∘ Dec) X509.CertPolFields
  parseCertPolFields =
    parseTLV _ "cert. policy" _
      (parseExactLength TLV.nonnesting (tell $ here' String.++ ": overflow") parseCertPolFieldsSeq)

open parseCertPolFields public using (parseCertPolFieldsSeq ; parseCertPolFields)


-- private
--   module Test where

--     val₁ : List UInt8
--     val₁ = # 4 ∷ # 26 ∷ # 48 ∷ # 24 ∷ # 48 ∷ # 8 ∷ # 6 ∷ # 6 ∷ # 103 ∷ # 129 ∷ # 12 ∷ # 1 ∷ # 2 ∷ # 1 ∷ # 48 ∷ # 12 ∷ # 6 ∷ # 10 ∷ # 43 ∷ # 6 ∷ # 1 ∷ # 4 ∷ # 1 ∷ # 214 ∷ # 121 ∷ # 2 ∷ # 5 ∷ [ # 3 ]

--     val₂ : List UInt8
--     val₂ = # 4 ∷ # 55 ∷ # 48 ∷ # 53 ∷ # 48 ∷ # 51 ∷ # 6 ∷ # 6 ∷ # 103 ∷ # 129 ∷ # 12 ∷ # 1 ∷ # 2 ∷ # 1 ∷ # 48 ∷ # 41 ∷ # 48 ∷ # 39 ∷ # 6 ∷ # 8 ∷ # 43 ∷ # 6 ∷ # 1 ∷ # 5 ∷ # 5 ∷ # 7 ∷ # 2 ∷ # 1 ∷ # 22 ∷ # 27 ∷ # 104 ∷ # 116 ∷ # 116 ∷ # 112 ∷ # 58 ∷ # 47 ∷ # 47 ∷ # 119 ∷ # 119 ∷ # 119 ∷ # 46 ∷ # 100 ∷ # 105 ∷ # 103 ∷ # 105 ∷ # 99 ∷ # 101 ∷ # 114 ∷ # 116 ∷ # 46 ∷ # 99 ∷ # 111 ∷ # 109 ∷ # 47 ∷ # 67 ∷ # 80 ∷ [ # 83 ]

--     val₃ : List UInt8
--     val₃ = # 4 ∷ # 54 ∷ # 48 ∷ # 52 ∷ # 48 ∷ # 50 ∷ # 6 ∷ # 4 ∷ # 85 ∷ # 29 ∷ # 32 ∷ # 0 ∷ # 48 ∷ # 42 ∷ # 48 ∷ # 40 ∷ # 6 ∷ # 8 ∷ # 43 ∷ # 6 ∷ # 1 ∷ # 5 ∷ # 5 ∷ # 7 ∷ # 2 ∷ # 1 ∷ # 22 ∷ # 28 ∷ # 104 ∷ # 116 ∷ # 116 ∷ # 112 ∷ # 115 ∷ # 58 ∷ # 47 ∷ # 47 ∷ # 119 ∷ # 119 ∷ # 119 ∷ # 46 ∷ # 100 ∷ # 105 ∷ # 103 ∷ # 105 ∷ # 99 ∷ # 101 ∷ # 114 ∷ # 116 ∷ # 46 ∷ # 99 ∷ # 111 ∷ # 109 ∷ # 47 ∷ # 67 ∷ # 80 ∷ [ # 83 ]

--     test₁ : X509.CertPolFields val₁
--     test₁ = Success.value (toWitness {Q = Logging.val (runParser parseCertPolFields val₁)} tt)

--     test₂ : X509.CertPolFields val₂
--     test₂ = Success.value (toWitness {Q = Logging.val (runParser parseCertPolFields val₂)} tt)

--     test₃ : X509.CertPolFields val₃
--     test₃ = Success.value (toWitness {Q = Logging.val (runParser parseCertPolFields val₃)} tt)
