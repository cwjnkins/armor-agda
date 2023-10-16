{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.Null.TCB
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parallel
import      Aeres.Grammar.Parser
open import Aeres.Prelude

module Aeres.Data.X690-DER.Null.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parallel    UInt8
open Aeres.Grammar.Parser      UInt8

private
  here' = "X690-DER: Null"

parse : Parser (Logging ∘ Dec) Null
parse =
  (parseTLV Tag.Null here' (_≡ [])
    (parseExactLength (λ where _ refl refl → refl) (tell $ here' String.++ ": nonzero length")
      (parseLit (return (Level.lift tt)) (return (Level.lift tt)) [])))

-- private
--   module Test where

--     Null₁ : List Dig
--     Null₁ = Tag.Null ∷ [ # 0 ]

--     Badnull₂ : List Dig
--     Badnull₂ = Tag.Null ∷ # 1 ∷ [ # 0 ]

--     test₁ : Null Null₁
--     test₁ = Success.value (toWitness {Q = Logging.val (runParser parseNull Null₁)} tt)

--     test₂ : ¬ Success _ Null Badnull₂
--     test₂ = toWitnessFalse {Q = Logging.val (runParser parseNull Badnull₂)} tt
