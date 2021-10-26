{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Decidable.TLV
open import Aeres.Grammar.Definitions
open import Aeres.Grammar.Parser

module Aeres.Data.X509.Decidable.Null where

open Base256

module parseNull where
  here' = "parseNull"

  open ≡-Reasoning

  parseNull : Parser Dig (Logging ∘ Dec) Generic.Null
  parseNull =
    (parseTLV Tag.Null "null" (_≡ [])
      (parseExactLength _ (λ where _ refl refl → refl) (tell $ here' String.++ ": nonzero length")
        (parseLit _ (return (Level.lift tt)) (return (Level.lift tt)) [])))

open parseNull public using (parseNull)
