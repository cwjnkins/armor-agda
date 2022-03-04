{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Decidable.Extension
import      Aeres.Grammar.Parser

module Aeres.Test.X509.GeneralName where

Gen₁ : List Dig
Gen₁ = Tag.EightyOne ∷ # 2 ∷ # 85 ∷ [ # 87 ]

Gen₂ : List Dig
Gen₂ = Tag.EightyEight ∷ # 2 ∷ # 134 ∷ [ # 72 ]

Gen₃ : List Dig
Gen₃ = Tag.A4 ∷ # 26 ∷ # 49 ∷ # 11  ∷ # 48  ∷ # 9  ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 4 ∷ # 6 ∷ # 19 ∷ # 2 ∷ # 85 ∷ # 83 ∷ # 49 ∷ # 11 ∷ # 48 ∷ # 9 ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 4 ∷ # 6 ∷ # 19 ∷ # 2 ∷ # 85 ∷ [ # 83 ]

test₁ : X509.GeneralName Gen₁
test₁ = Success.value (toWitness {Q = Logging.val (runParser parseGeneralName Gen₁)} tt)

test₂ : X509.GeneralName Gen₂
test₂ = Success.value (toWitness {Q = Logging.val (runParser parseGeneralName Gen₂)} tt)

test₃ : X509.GeneralName Gen₃
test₃ = Success.value (toWitness {Q = Logging.val (runParser parseGeneralName Gen₃)} tt)
