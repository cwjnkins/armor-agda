{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Decidable.Bitstring
open import Aeres.Data.X509.Decidable.Length
open import Aeres.Data.X509.Decidable.SignAlg
open import Aeres.Data.X509.Decidable.TLV
open import Aeres.Data.X509.Properties as Props
open import Aeres.Grammar.Definitions
open import Aeres.Grammar.Parser
open import Data.List.Properties
open import Data.Nat.Properties
  hiding (_≟_)
-- open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Decidable.PublicKey where

open Base256

module parsePublicKeyFields where
  here' = "parsePublicKeyFields"

  open ≡-Reasoning

  parsePublicKeyFields : Parser Dig (Logging ∘ Dec) X509.PublicKeyFields
  runParser parsePublicKeyFields xs = do
    yes r ← runParser (parse& _ Props.TLV.nonnesting parseSignAlg parseBitstring) xs
      where no ¬parse → do
        tell here'
        return ∘ no $ λ where
          r →
            contradiction
              (mapSuccess _ (λ where (X509.mkPublicKeyFields signalg pubkey bs≡) → mk&ₚ signalg pubkey bs≡) r)
              ¬parse
    return (yes
      (mapSuccess _ (λ where (mk&ₚ fstₚ₁ sndₚ₁ bs≡) → X509.mkPublicKeyFields fstₚ₁ sndₚ₁ bs≡) r))

open parsePublicKeyFields public using (parsePublicKeyFields)

parsePublicKey : Parser Dig (Logging ∘ Dec) X509.PublicKey
parsePublicKey =
  parseTLV _ "publick key" _
    (parseExactLength _ Props.PublicKeyFields.nonnesting (tell "public key: length mismatch") parsePublicKeyFields)
