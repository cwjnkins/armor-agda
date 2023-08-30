{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Prelude
open import Aeres.Data.UTF8
open import Aeres.Data.X509.Strings.Properties
open import Aeres.Data.X509.Strings.TCB
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Data.X690-DER.OctetString
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.IList
import      Aeres.Grammar.Parser

module Aeres.Data.X509.Strings.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.IList       UInt8
open Aeres.Grammar.Parser      UInt8

parseTeletexString : Parser (Logging ∘ Dec) TeletexString
parseTeletexString =
  parseTLV Tag.TeletexString "teletex string" OctetStringValue parseOctetStringValue

parseUniversalString : Parser (Logging ∘ Dec) UniversalString
parseUniversalString =
  parseTLV Tag.UniversalString "universal string" _ parseUTF8

parseUTF8String : Parser (Logging ∘ Dec) UTF8String
parseUTF8String =
  parseTLV Tag.UTF8String "UTF8 string" _ parseUTF8

parseBMPString : Parser (Logging ∘ Dec) BMPString
parseBMPString =
  parseTLV Tag.BMPString "BMP string" _
    (parseIList
      (tell "parseBMPString: underflow") _
      BMP.nonempty BMP.nonnesting
      p)
  where
  p : Parser (Logging ∘ Dec) BMPChar
  runParser p xs = do
    yes (success ._ _ refl (mk×ₚ (singleton (c₁ ∷ c₂ ∷ []) refl) (─ refl) refl) suf₁ refl)
      ← runParser (parseN 2 (tell "parseBMP: underflow")) xs
      where no ¬p → do
        return ∘ no $ λ where
          (success ._ ._ refl (mkBMPChar c₁ c₂ range refl) ._ refl) →
            contradiction (success _ _ refl (mk×ₚ (singleton (c₁ ∷ [ c₂ ]) refl) (─ refl) refl) _ refl) ¬p
    case inRange? 0 215 c₁ of λ where
      (yes c₁≤215) →
        return (yes (success _ _ refl (mkBMPChar c₁ c₂ (inj₁ c₁≤215) refl) suf₁ refl))
      (no ¬c₁≤215) →
        case inRange? 224 255 c₁ of λ where
          (yes r) → return (yes (success _ _ refl (mkBMPChar c₁ c₂ (inj₂ r) refl) suf₁ refl))
          (no ¬r) → do
            tell $ "parseBMP: char 1 out of range: " String.++ (show (toℕ c₁))
            return ∘ no $ λ where
              (success ._ _ refl (mkBMPChar .c₁ .c₂ range refl) _ refl) →
                ‼ (case range of λ where
                  (inj₁ p) → contradiction p ¬c₁≤215
                  (inj₂ p) → contradiction p ¬r)

parseVisibleString : Parser (Logging ∘ Dec) VisibleString
parseVisibleString =
  parseTLV Tag.VisibleString "universal string" _ parseUTF8

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
