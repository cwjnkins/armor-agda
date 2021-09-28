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

module Aeres.Data.X509.Decidable.Octetstring where

open Base256

module parseOctetstring where
  here' = "parseOctetString"

  open ≡-Reasoning

  parseOctetstring : Parser Dig (Logging ∘ Dec) Generic.Octetstring
  parseOctetstring =
    parseTLV Tag.Octetstring "octetstring" (Singleton (List Dig))
      λ n → parseN Dig n (tell $ here' String.++ ": underflow")

open parseOctetstring public using (parseOctetstring)
