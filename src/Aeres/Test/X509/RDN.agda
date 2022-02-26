{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Decidable.RDN
open import Aeres.Grammar.Definitions
open import Aeres.Grammar.Parser
open import Aeres.Prelude

module Aeres.Test.X509.RDN where

open Base256

Name₁ : List Dig
Name₁ = Tag.Sequence ∷ # 26 ∷ # 49 ∷ # 11  ∷ # 48  ∷ # 9  ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 4 ∷ # 6 ∷ # 19 ∷ # 2 ∷ # 85 ∷ # 83 ∷ # 49 ∷ # 11 ∷ # 48 ∷ # 9 ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 4 ∷ # 6 ∷ # 19 ∷ # 2 ∷ # 85 ∷ [ # 83 ]

Name₂ : List Dig
Name₂ = Tag.Sequence ∷ # 26 ∷ # 49 ∷ # 11  ∷ # 48  ∷ # 9  ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 4 ∷ # 6 ∷ # 19 ∷ # 2 ∷ # 85 ∷ # 83 ∷ # 48 ∷ # 11 ∷ # 49 ∷ # 9 ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 4 ∷ # 6 ∷ # 19 ∷ # 2 ∷ # 85 ∷ [ # 83 ]

test₁ : X509.RDNSeq Name₁
test₁ = Success.value (toWitness {Q = Logging.val (runParser parseRDNSeq Name₁)} tt)

test₂ : ¬ Success _ X509.RDNSeq Name₂
test₂ = toWitnessFalse {Q = Logging.val (runParser parseRDNSeq Name₂)} tt
