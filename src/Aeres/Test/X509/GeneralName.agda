{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Decidable.GeneralName
open import Aeres.Data.X690-DER
import      Aeres.Grammar.Parser

module Aeres.Test.X509.GeneralName where

open Aeres.Grammar.Parser UInt8

Gen₁ : List UInt8
Gen₁ = Tag.A81 ∷ # 2 ∷ # 85 ∷ [ # 87 ]

Gen₂ : List UInt8
Gen₂ = Tag.A88 ∷ # 2 ∷ # 134 ∷ [ # 72 ]

Gen₃ : List UInt8
Gen₃ = Tag.AA4 ∷ # 26 ∷ # 49 ∷ # 11  ∷ # 48  ∷ # 9  ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 4 ∷ # 6 ∷ # 19 ∷ # 2 ∷ # 85 ∷ # 83 ∷ # 49 ∷ # 11 ∷ # 48 ∷ # 9 ∷ # 6 ∷ # 3 ∷ # 85 ∷ # 4 ∷ # 6 ∷ # 19 ∷ # 2 ∷ # 85 ∷ [ # 83 ]

test₁ : X509.GeneralName Gen₁
test₁ = Success.value (toWitness {Q = Logging.val (runParser parseGeneralName Gen₁)} tt)

test₂ : X509.GeneralName Gen₂
test₂ = Success.value (toWitness {Q = Logging.val (runParser parseGeneralName Gen₂)} tt)

test₃ : X509.GeneralName Gen₃
test₃ = Success.value (toWitness {Q = Logging.val (runParser parseGeneralName Gen₃)} tt)
