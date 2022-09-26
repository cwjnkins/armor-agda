{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Properties as Props
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

  parseBoolValue : Parser Dig (Logging ∘ Dec) BoolValue
  runParser parseBoolValue [] = do
    tell $ here' String.++ ": underflow"
    return ∘ no $ λ where
      (success prefix read read≡ value suffix ps≡) →
        contradiction (++-conicalˡ _ suffix ps≡) (Boool.nonempty value)
  runParser parseBoolValue (x ∷ xs)
    with x ≟ # 0
  ... | yes refl =
    return (yes (success [ # 0 ] _ refl (mkBoolValue false (# 0) falseᵣ refl) xs refl))
  ... | no x≢0
    with x ≟ # 255
  ... | yes refl =
    return (yes (success [ # 255 ] _ refl (mkBoolValue true (# 255) trueᵣ refl) xs refl))
  ... | no  x≢255 = do
    tell $ here' String.++ ": invalid boolean rep"
    return ∘ no $ λ where
      (success prefix _ _ (mkBoolValue v _ vᵣ refl) suffix ps≡) → ‼
        (case vᵣ of λ where
          falseᵣ → contradiction (∷-injectiveˡ (sym ps≡)) x≢0
          trueᵣ  → contradiction (∷-injectiveˡ (sym ps≡)) x≢255)

  parseBool : Parser Dig (Logging ∘ Dec) Boool
  parseBool = parseTLV Tag.Boolean "bool" BoolValue
                (parseExactLength _ Boool.nonnesting (tell $ here' String.++ "bad length for bool") parseBoolValue)

open parseBool public using (parseBoolValue ; parseBool)


private
  module Test where

    tval : List Dig
    tval = Tag.Boolean ∷ # 1 ∷ [ # 255 ]

    fval : List Dig
    fval = Tag.Boolean ∷ # 1 ∷ [ # 0 ]

    badval : List Dig
    badval = Tag.Boolean ∷ # 1 ∷ [ # 20 ]

    test₁ : Boool tval
    test₁ = Success.value (toWitness {Q = Logging.val (runParser parseBool tval)} tt)

    test₂ : Boool fval
    test₂ = Success.value (toWitness {Q = Logging.val (runParser parseBool fval)} tt)

    test₃ : ¬ Success _ Boool badval
    test₃ = toWitnessFalse {Q = Logging.val (runParser parseBool badval)} tt
