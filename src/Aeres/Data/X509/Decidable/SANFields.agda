{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Decidable.GeneralName
open import Aeres.Data.X509.Properties as Props
open import Aeres.Grammar.Definitions
open import Aeres.Grammar.Parser
open import Data.List.Properties
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Decidable.SANFields where

open Base256

module parseSANFields where
  here' = "parseSANFields"

  open ≡-Reasoning

  parseSANFields : Parser Dig (Logging ∘ Dec) X509.SANFields
  parseSANFields =
    parseTLV _ "SAN Fields" _
      (parseExactLength _ TLV.nonnesting
        (tell $ here' String.++ ": underflow")
          (parseNonEmptySeq "SAN Fields Elems" _
            Props.GeneralName.nonempty Props.GeneralName.nonnesting parseGeneralName))


open parseSANFields public using (parseSANFields)

private
  module Test where

    val₁ : List Dig
    val₁ = # 4 ∷ # 130 ∷ # 1 ∷ # 121 ∷ # 48 ∷ # 130 ∷ # 1 ∷ # 117 ∷ # 130 ∷ # 10 ∷ # 97 ∷ # 109 ∷ # 97 ∷ # 122 ∷ # 111 ∷ # 110 ∷ # 46 ∷ # 99 ∷ # 111 ∷ # 109 ∷ # 130 ∷ # 8 ∷ # 97 ∷ # 109 ∷ # 122 ∷ # 110 ∷ # 46 ∷ # 99 ∷ # 111 ∷ # 109 ∷ # 130 ∷ # 17 ∷ # 117 ∷ # 101 ∷ # 100 ∷ # 97 ∷ # 116 ∷ # 97 ∷ # 46 ∷ # 97 ∷ # 109 ∷ # 97 ∷ # 122 ∷ # 111 ∷ # 110 ∷ # 46 ∷ # 99 ∷ # 111 ∷ # 109 ∷ # 130 ∷ # 13 ∷ # 117 ∷ # 115 ∷ # 46 ∷ # 97 ∷ # 109 ∷ # 97 ∷ # 122 ∷ # 111 ∷ # 110 ∷ # 46 ∷ # 99 ∷ # 111 ∷ # 109 ∷ # 130 ∷ # 14 ∷ # 119 ∷ # 119 ∷ # 119 ∷ # 46 ∷ # 97 ∷ # 109 ∷ # 97 ∷ # 122 ∷ # 111 ∷ # 110 ∷ # 46 ∷ # 99 ∷ # 111 ∷ # 109 ∷ # 130 ∷ # 12 ∷ # 119 ∷ # 119 ∷ # 119 ∷ # 46 ∷ # 97 ∷ # 109 ∷ # 122 ∷ # 110 ∷ # 46 ∷ # 99 ∷ # 111 ∷ # 109 ∷ # 130 ∷ # 20 ∷ # 99 ∷ # 111 ∷ # 114 ∷ # 112 ∷ # 111 ∷ # 114 ∷ # 97 ∷ # 116 ∷ # 101 ∷ # 46 ∷ # 97 ∷ # 109 ∷ # 97 ∷ # 122 ∷ # 111 ∷ # 110 ∷ # 46 ∷ # 99 ∷ # 111 ∷ # 109 ∷ # 130 ∷ # 17 ∷ # 98 ∷ # 117 ∷ # 121 ∷ # 98 ∷ # 111 ∷ # 120 ∷ # 46 ∷ # 97 ∷ # 109 ∷ # 97 ∷ # 122 ∷ # 111 ∷ # 110 ∷ # 46 ∷ # 99 ∷ # 111 ∷ # 109 ∷ # 130 ∷ # 17 ∷ # 105 ∷ # 112 ∷ # 104 ∷ # 111 ∷ # 110 ∷ # 101 ∷ # 46 ∷ # 97 ∷ # 109 ∷ # 97 ∷ # 122 ∷ # 111 ∷ # 110 ∷ # 46 ∷ # 99 ∷ # 111 ∷ # 109 ∷ # 130 ∷ # 13 ∷ # 121 ∷ # 112 ∷ # 46 ∷ # 97 ∷ # 109 ∷ # 97 ∷ # 122 ∷ # 111 ∷ # 110 ∷ # 46 ∷ # 99 ∷ # 111 ∷ # 109 ∷ # 130 ∷ # 15 ∷ # 104 ∷ # 111 ∷ # 109 ∷ # 101 ∷ # 46 ∷ # 97 ∷ # 109 ∷ # 97 ∷ # 122 ∷ # 111 ∷ # 110 ∷ # 46 ∷ # 99 ∷ # 111 ∷ # 109 ∷ # 130 ∷ # 21 ∷ # 111 ∷ # 114 ∷ # 105 ∷ # 103 ∷ # 105 ∷ # 110 ∷ # 45 ∷ # 119 ∷ # 119 ∷ # 119 ∷ # 46 ∷ # 97 ∷ # 109 ∷ # 97 ∷ # 122 ∷ # 111 ∷ # 110 ∷ # 46 ∷ # 99 ∷ # 111 ∷ # 109 ∷ # 130 ∷ # 33 ∷ # 98 ∷ # 117 ∷ # 99 ∷ # 107 ∷ # 101 ∷ # 121 ∷ # 101 ∷ # 45 ∷ # 114 ∷ # 101 ∷ # 116 ∷ # 97 ∷ # 105 ∷ # 108 ∷ # 45 ∷ # 119 ∷ # 101 ∷ # 98 ∷ # 115 ∷ # 105 ∷ # 116 ∷ # 101 ∷ # 46 ∷ # 97 ∷ # 109 ∷ # 97 ∷ # 122 ∷ # 111 ∷ # 110 ∷ # 46 ∷ # 99 ∷ # 111 ∷ # 109 ∷ # 130 ∷ # 18 ∷ # 104 ∷ # 117 ∷ # 100 ∷ # 100 ∷ # 108 ∷ # 101 ∷ # 115 ∷ # 46 ∷ # 97 ∷ # 109 ∷ # 97 ∷ # 122 ∷ # 111 ∷ # 110 ∷ # 46 ∷ # 99 ∷ # 111 ∷ # 109 ∷ # 130 ∷ # 37 ∷ # 112 ∷ # 45 ∷ # 110 ∷ # 116 ∷ # 45 ∷ # 119 ∷ # 119 ∷ # 119 ∷ # 45 ∷ # 97 ∷ # 109 ∷ # 97 ∷ # 122 ∷ # 111 ∷ # 110 ∷ # 45 ∷ # 99 ∷ # 111 ∷ # 109 ∷ # 45 ∷ # 107 ∷ # 97 ∷ # 108 ∷ # 105 ∷ # 97 ∷ # 115 ∷ # 46 ∷ # 97 ∷ # 109 ∷ # 97 ∷ # 122 ∷ # 111 ∷ # 110 ∷ # 46 ∷ # 99 ∷ # 111 ∷ # 109 ∷ # 130 ∷ # 37 ∷ # 112 ∷ # 45 ∷ # 121 ∷ # 111 ∷ # 45 ∷ # 119 ∷ # 119 ∷ # 119 ∷ # 45 ∷ # 97 ∷ # 109 ∷ # 97 ∷ # 122 ∷ # 111 ∷ # 110 ∷ # 45 ∷ # 99 ∷ # 111 ∷ # 109 ∷ # 45 ∷ # 107 ∷ # 97 ∷ # 108 ∷ # 105 ∷ # 97 ∷ # 115 ∷ # 46 ∷ # 97 ∷ # 109 ∷ # 97 ∷ # 122 ∷ # 111 ∷ # 110 ∷ # 46 ∷ # 99 ∷ # 111 ∷ # 109 ∷ # 130 ∷ # 37 ∷ # 112 ∷ # 45 ∷ # 121 ∷ # 51 ∷ # 45 ∷ # 119 ∷ # 119 ∷ # 119 ∷ # 45 ∷ # 97 ∷ # 109 ∷ # 97 ∷ # 122 ∷ # 111 ∷ # 110 ∷ # 45 ∷ # 99 ∷ # 111 ∷ # 109 ∷ # 45 ∷ # 107 ∷ # 97 ∷ # 108 ∷ # 105 ∷ # 97 ∷ # 115 ∷ # 46 ∷ # 97 ∷ # 109 ∷ # 97 ∷ # 122 ∷ # 111 ∷ # 110 ∷ # 46 ∷ # 99 ∷ # 111 ∷ [ # 109 ]

    test₁ : X509.SANFields val₁
    test₁ = Success.value (toWitness {Q = Logging.val (runParser parseSANFields val₁)} tt)
