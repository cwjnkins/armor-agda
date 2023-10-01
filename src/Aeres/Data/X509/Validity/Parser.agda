{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.Validity.TCB
open import Aeres.Data.X509.Validity.Properties
open import Aeres.Data.X690-DER
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parallel
import      Aeres.Grammar.Parser
import      Aeres.Grammar.Seq
open import Aeres.Prelude

module Aeres.Data.X509.Validity.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parallel    UInt8
open Aeres.Grammar.Parser      UInt8
open Aeres.Grammar.Seq         UInt8

module parseValidityFields where
  here' = "parseValidityFields"

  open ≡-Reasoning

  parseValidityFields : Parser (Logging ∘ Dec) ValidityFields
  runParser parseValidityFields xs = do
    yes (success pre₀ r₀ r₀≡ v₀ suf₀ ps≡₀)
      ← runParser (parse& Time.nosubstrings parseTime parseTime) xs
      where no ¬parse → do
        tell $ here'
        return ∘ no $ λ where
          (success ._ read read≡ (mkValidityFields{nb = nb}{na} start end refl) suffix ps≡) →
            contradiction (success _ _ read≡ (mk&ₚ start end refl) suffix ps≡) ¬parse
    return (yes (success pre₀ _ r₀≡ (mkValidityFields (fstₚ v₀) (sndₚ v₀) (&ₚᵈ.bs≡ v₀)) _ ps≡₀))

open parseValidityFields public using (parseValidityFields)

parseValidity : Parser (Logging ∘ Dec) Validity
parseValidity =
  parseTLV _ "Validity" _
    (parseExactLength nosubstrings (tell $ "validity: length mismatch") parseValidityFields)


-- private
--   module Test where

--     Validity₁ : List Dig
--     Validity₁ = Tag.Sequence ∷ # 32 ∷ # Tag.GeneralizedTime ∷ # 15 ∷ # 50 ∷ # 56 ∷ # 52 ∷ # 49 ∷ # 48 ∷ # 54 ∷ # 50 ∷ # 52 ∷ # 49 ∷ # 56 ∷ # 51 ∷ # 54 ∷ # 53 ∷ # 52 ∷ # 90 ∷ # Tag.UTCTime ∷ # 13 ∷ # 57 ∷ # 55 ∷ # 48 ∷ # 53 ∷ # 51 ∷ # 48 ∷ # 49 ∷ # 52 ∷ # 52 ∷ # 56 ∷ # 50 ∷ # 50 ∷ [ # 90 ]

--     test₁ : Validity Validity₁
--     test₁ = Success.value (toWitness {Q = Logging.val (runParser parseValidity Validity₁)} tt)
