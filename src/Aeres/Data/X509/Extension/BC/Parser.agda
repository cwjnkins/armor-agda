{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.Extension.BC.Properties
open import Aeres.Data.X509.Extension.BC.TCB
open import Aeres.Data.X690-DER.Boool
open import Aeres.Data.X690-DER.Int
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
import      Aeres.Grammar.Parallel
import      Aeres.Grammar.Parser
open import Aeres.Prelude

module Aeres.Data.X509.Extension.BC.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8
open Aeres.Grammar.Parallel    UInt8
open Aeres.Grammar.Parser      UInt8

private
  here' = "X509: Extension: BC"

postulate
  parseBCFieldsSeqFields : ∀ n → Parser (Logging ∘ Dec) (ExactLength BCFieldsSeqFields n)
-- parseBCFieldsSeqFields n =
  -- parseEquivalent (Parallel.equivalent₁ equivalent)
  --   (Option.parseOption₂ TLV.nosubstrings TLV.nosubstrings
  --     (TLV.noconfusion λ where ())
  --     parseBool
  --     (Int.parse here')
  --     (tell $ here' String.++ ": underflow") _)
  -- {!!}

parseBCFieldsSeq : Parser (Logging ∘ Dec) BCFieldsSeq
parseBCFieldsSeq = parseTLV _ (here' String.++ ": Seq") _ parseBCFieldsSeqFields

parseBCFields : Parser (Logging ∘ Dec) BCFields
parseBCFields = parseTLV _ here' _ (parseExactLength TLV.nosubstrings (tell $ here' String.++ ": underflow") parseBCFieldsSeq)

-- private
--   module Test where

--     val₁ : List Dig
--     val₁ = # 4 ∷ # 2 ∷ # 48 ∷ [ # 0 ]

--     val₂ : List Dig
--     val₂ = # 4 ∷ # 5 ∷ # 48 ∷ # 3 ∷ # 1 ∷ # 1 ∷ [ # 255 ]

--     val₃ : List Dig
--     val₃ = # 4 ∷ # 8 ∷ # 48 ∷ # 6 ∷ # 1 ∷ # 1 ∷ # 255 ∷ # 2 ∷ # 1 ∷ [ # 0 ]

--     test₁ : X509.BCFields val₁
--     test₁ = Success.value (toWitness {Q = Logging.val (runParser parseBCFields val₁)} tt)

--     test₂ : X509.BCFields val₂
--     test₂ = Success.value (toWitness {Q = Logging.val (runParser parseBCFields val₂)} tt)

--     test₃ : X509.BCFields val₃
--     test₃ = Success.value (toWitness {Q = Logging.val (runParser parseBCFields val₃)} tt)
