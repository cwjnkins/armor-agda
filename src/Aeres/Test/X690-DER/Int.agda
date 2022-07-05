{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER
open import Aeres.Grammar.Parser
open import Aeres.Prelude

module Aeres.Test.X690-DER.Int where

intval₁ : List UInt8
intval₁ = Tag.Integer ∷ # 1 ∷ [ # 255 ]

intval₂ : List UInt8
intval₂ = Tag.Integer ∷ # 2 ∷ # 254 ∷ [ # 255 ]

intvalBad : List UInt8
intvalBad = Tag.Integer ∷ # 4 ∷ # 254 ∷ [ # 255 ]

test₁ : Int intval₁
test₁ = Success.value (toWitness {Q = Logging.val (runParser parseInt intval₁)} tt)

test₂ : Int intval₂
test₂ = Success.value (toWitness {Q = Logging.val (runParser parseInt intval₂)} tt)

test₃ : ¬ Success _ Int intvalBad
test₃ = toWitnessFalse {Q = Logging.val (runParser parseInt intvalBad)} tt
