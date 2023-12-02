open import Aeres.Binary
open import Aeres.Prelude
open import Aeres.Data.Unicode.UTF16
open import Aeres.Data.X690-DER.Strings.BMPString.TCB
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Data.X690-DER.OctetString
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.IList
import      Aeres.Grammar.Parser

module Aeres.Data.X690-DER.Strings.BMPString.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.IList       UInt8
open Aeres.Grammar.Parser      UInt8

private
  here' = "X690-DER: Strings: BMPString: parse:"

parseBMPString : Parser (Logging ∘ Dec) BMPString
parseBMPString =
  parseTLV Tag.BMPString here' _ parseBMP

-- private
--   module Test where

--   Oct₁ : List UInt8
--   Oct₁ = Tag.OctetString ∷ # 2 ∷ # 1 ∷ [ # 1 ]

--   -- I5₂ : List UInt8
--   -- I5₂ = Tag.IA5String ∷ # 2 ∷ # 1 ∷ [ # 1 ]

--   -- I5₃ : List UInt8
--   -- I5₃ = Tag.IA5String ∷ # 2 ∷ # 1 ∷ [ # 160 ]

--   test₁ : OctetString Oct₁
--   test₁ = Success.value (toWitness {Q = Logging.val (runParser parseOctetString Oct₁)} tt)

--   -- test₂ :  IA5String I5₂
--   -- test₂ = Success.value (toWitness {Q = Logging.val (runParser parseIA5String I5₂)} tt)

--   -- test₃ : ¬ Success IA5String I5₃
