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

module Aeres.Data.X509.Decidable.SignAlg where

open Base256

postulate
  parseSignAlgFields : ∀ n → Parser Dig (Logging ∘ Dec) (ExactLength _ X509.SignAlgFields n)

parseSignAlg : Parser Dig (Logging ∘ Dec) X509.SignAlg
parseSignAlg =
  parseTLV _ "signature algorithm" _ parseSignAlgFields
