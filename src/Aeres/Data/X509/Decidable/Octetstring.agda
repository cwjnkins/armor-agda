{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.UTF8
open import Aeres.Data.X509
open import Aeres.Data.X509.Properties
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parser
open import Data.List.Properties
open import Data.Nat.Properties
  hiding (_≟_)

module Aeres.Data.X509.Decidable.Octetstring where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parser      UInt8

parseTeletexString : Parser (Logging ∘ Dec) X509.TeletexString
parseTeletexString =
  parseTLV Tag.TeletexString "teletex string" OctetStringValue parseOctetStringValue

parseUniversalString : Parser (Logging ∘ Dec) X509.UniversalString
parseUniversalString =
  parseTLV Tag.UniversalString "universal string" _ parseUTF8

parseUTF8String : Parser (Logging ∘ Dec) X509.UTF8String
parseUTF8String =
  parseTLV Tag.UTF8String "UTF8 string" _ parseUTF8

parseBMPString : Parser (Logging ∘ Dec) X509.BMPString
parseBMPString =
  parseTLV Tag.BMPString "BMP string" _ parseUTF8

parseVisibleString : Parser (Logging ∘ Dec) X509.VisibleString
parseVisibleString =
  parseTLV Tag.VisibleString "universal string" _ parseUTF8

private
  module Test where

  Oct₁ : List UInt8
  Oct₁ = Tag.OctetString ∷ # 2 ∷ # 1 ∷ [ # 1 ]

  -- I5₂ : List UInt8
  -- I5₂ = Tag.IA5String ∷ # 2 ∷ # 1 ∷ [ # 1 ]

  -- I5₃ : List UInt8
  -- I5₃ = Tag.IA5String ∷ # 2 ∷ # 1 ∷ [ # 160 ]

  test₁ : OctetString Oct₁
  test₁ = Success.value (toWitness {Q = Logging.val (runParser parseOctetString Oct₁)} tt)

  -- test₂ :  IA5String I5₂
  -- test₂ = Success.value (toWitness {Q = Logging.val (runParser parseIA5String I5₂)} tt)

  -- test₃ : ¬ Success IA5String I5₃
  -- test₃ = toWitnessFalse {Q = Logging.val (runParser parseIA5String I5₃)} tt
