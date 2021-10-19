{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Decidable.Length
open import Aeres.Data.X509.Decidable.Time
open import Aeres.Data.X509.Decidable.TLV
open import Aeres.Data.X509.Properties as Props
open import Aeres.Grammar.Definitions
open import Aeres.Grammar.Parser
open import Data.List.Properties
open import Data.Nat.Properties
  hiding (_≟_)
-- open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Decidable.Validity where

open Base256

module parseValidityFields where
  here' = "parseValidityFields"

  open ≡-Reasoning

  parseValidityFields : Parser Dig (Logging ∘ Dec) X509.ValidityFields
  runParser parseValidityFields xs = do
    yes (success pre₀ r₀ r₀≡ v₀ suf₀ ps≡₀)
      ← runParser (parse& Dig Props.Time.nonnesting parseTime parseTime) xs
      where no ¬parse → do
        tell $ here'
        return ∘ no $ λ where
          (success ._ read read≡ (X509.mkValidityFields{nb = nb}{na} start end refl) suffix ps≡) →
            contradiction (success _ _ read≡ (mk&ₚ start end refl) suffix ps≡) ¬parse
    return (yes (success pre₀ _ r₀≡ (X509.mkValidityFields (fstₚ v₀) (sndₚ v₀) (&ₚ.bs≡ v₀)) _ ps≡₀))

open parseValidityFields public using (parseValidityFields)

parseValidity : Parser Dig (Logging ∘ Dec) X509.Validity
parseValidity =
  parseTLV _ "Validity" _
    (parseExactLength _ NonNesting.ValidityFields (tell $ "validity: length mismatch") parseValidityFields)