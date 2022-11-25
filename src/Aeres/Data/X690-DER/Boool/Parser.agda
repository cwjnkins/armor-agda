{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.Boool.Properties
open import Aeres.Data.X690-DER.Boool.TCB
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parser
open import Aeres.Prelude
-- open import Data.List.Properties
-- open import Data.Nat.Properties
--   hiding (_≟_)
-- open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X690-DER.Boool.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parser      UInt8

private
  here' = "X690-DER: Bool"

parseBoolValue : Parser (Logging ∘ Dec) BoolValue
runParser parseBoolValue [] = do
  tell $ here' String.++ ": underflow"
  return ∘ no $ λ where
    (success prefix read read≡ value suffix ps≡) →
      contradiction (++-conicalˡ _ suffix ps≡) (nonempty value)
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

parseBool : Parser (Logging ∘ Dec) Boool
parseBool = parseTLV Tag.Boolean here' BoolValue
              (parseExactLength nonnesting (tell $ here' String.++ "bad length for bool") parseBoolValue)


-- private
--   module Test where

--     tval : List Dig
--     tval = Tag.Boolean ∷ # 1 ∷ [ # 255 ]

--     fval : List Dig
--     fval = Tag.Boolean ∷ # 1 ∷ [ # 0 ]

--     badval : List Dig
--     badval = Tag.Boolean ∷ # 1 ∷ [ # 20 ]

--     test₁ : Boool tval
--     test₁ = Success.value (toWitness {Q = Logging.val (runParser parseBool tval)} tt)

--     test₂ : Boool fval
--     test₂ = Success.value (toWitness {Q = Logging.val (runParser parseBool fval)} tt)

--     test₃ : ¬ Success _ Boool badval
--     test₃ = toWitnessFalse {Q = Logging.val (runParser parseBool badval)} tt
