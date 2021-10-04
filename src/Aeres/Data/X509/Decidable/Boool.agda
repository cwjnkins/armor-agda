{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Decidable.Length
open import Aeres.Data.X509.Decidable.TLV
open import Aeres.Data.X509.Properties
open import Aeres.Grammar.Definitions
open import Aeres.Grammar.Parser
open import Data.List.Properties
open import Data.Nat.Properties
  hiding (_≟_)
-- open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Decidable.Boool where

open Base256

module parseBool where
  here' = "parseBool"

  open ≡-Reasoning

  parseBoolValue : Parser Dig (Logging ∘ Dec) Generic.BoolValue
  runParser parseBoolValue [] = do
    tell $ here' String.++ ": underflow"
    return ∘ no $ λ where
      (success prefix read read≡ value suffix ps≡) →
        contradiction (++-conicalˡ _ suffix ps≡) (NonEmpty.BoolValue value)
  runParser parseBoolValue (x ∷ xs)
    with x ≟ # 0
  ... | yes refl =
    return (yes (success [ # 0 ] _ refl (Generic.mkBoolValue false (# 0) Generic.falseᵣ refl) xs refl))
  ... | no x≢0
    with x ≟ # 255
  ... | yes refl =
    return (yes (success [ # 255 ] _ refl (Generic.mkBoolValue true (# 255) Generic.trueᵣ refl) xs refl))
  ... | no  x≢255 = do
    tell $ here' String.++ ": invalid boolean rep"
    return ∘ no $ λ where
      (success prefix _ _ (Generic.mkBoolValue v _ vᵣ refl) suffix ps≡) → ‼
        (case vᵣ of λ where
          Generic.falseᵣ → contradiction (∷-injectiveˡ (sym ps≡)) x≢0
          Generic.trueᵣ  → contradiction (∷-injectiveˡ (sym ps≡)) x≢255)

  parseBool : Parser Dig (Logging ∘ Dec) Generic.Boool
  parseBool = parseTLV Tag.Boolean "bool" Generic.BoolValue
                (parseExactLength _ NonNesting.BoolValue (tell $ here' String.++ "bad length for bool") parseBoolValue)

open parseBool public using (parseBoolValue ; parseBool)