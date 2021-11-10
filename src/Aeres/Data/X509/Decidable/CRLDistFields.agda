{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Decidable.DistPoint
open import Aeres.Data.X509.Decidable.Length
open import Aeres.Data.X509.Decidable.Seq
open import Aeres.Data.X509.Decidable.TLV
open import Aeres.Data.X509.Properties as Props
open import Aeres.Grammar.Definitions
open import Aeres.Grammar.Parser
open import Data.List.Properties
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Decidable.CRLDistFields where

open Base256

module parseCRLDistFields where
  here' = "parseCRLDistFields"

  open ≡-Reasoning

  parseCRLDistFields : Parser Dig (Logging ∘ Dec) X509.CRLDistFields
  parseCRLDistFields = parseTLV _ "CRL Dist Fields" _ (parseExactLength _ Props.TLV.nonnesting (tell $ here' String.++ ": underflow")
    (parseSeq "CRL Dist Fields Elems" _ Props.TLV.nonempty Props.TLV.nonnesting parseDistPoint))


open parseCRLDistFields public using (parseCRLDistFields)

private
  module Test where

    val₁ : List Dig
    val₁ = # 4 ∷ # 53 ∷ # 48 ∷ # 51 ∷ # 48 ∷ # 49 ∷ # 160 ∷ # 47 ∷ # 160 ∷ # 45 ∷ # 134 ∷ # 43 ∷ # 104 ∷ # 116 ∷ # 116 ∷ # 112 ∷ # 58 ∷ # 47 ∷ # 47 ∷ # 99 ∷ # 114 ∷ # 108 ∷ # 115 ∷ # 46 ∷ # 112 ∷ # 107 ∷ # 105 ∷ # 46 ∷ # 103 ∷ # 111 ∷ # 111 ∷ # 103 ∷ # 47 ∷ # 103 ∷ # 116 ∷ # 115 ∷ # 49 ∷ # 99 ∷ # 51 ∷ # 47 ∷ # 122 ∷ # 100 ∷ # 65 ∷ # 84 ∷ # 116 ∷ # 48 ∷ # 69 ∷ # 120 ∷ # 95 ∷ # 70 ∷ # 107 ∷ # 46 ∷ # 99 ∷ # 114 ∷ [ # 108 ]

    val₂ : List Dig
    val₂ = # 4 ∷ # 112 ∷ # 48 ∷ # 110 ∷ # 48 ∷ # 53 ∷ # 160 ∷ # 51 ∷ # 160 ∷ # 49 ∷ # 134 ∷ # 47 ∷ # 104 ∷ # 116 ∷ # 116 ∷ # 112 ∷ # 58 ∷ # 47 ∷ # 47 ∷ # 99 ∷ # 114 ∷ # 108 ∷ # 51 ∷ # 46 ∷ # 100 ∷ # 105 ∷ # 103 ∷ # 105 ∷ # 99 ∷ # 101 ∷ # 114 ∷ # 116 ∷ # 46 ∷ # 99 ∷ # 111 ∷ # 109 ∷ # 47 ∷ # 68 ∷ # 105 ∷ # 103 ∷ # 105 ∷ # 67 ∷ # 101 ∷ # 114 ∷ # 116 ∷ # 71 ∷ # 108 ∷ # 111 ∷ # 98 ∷ # 97 ∷ # 108 ∷ # 67 ∷ # 65 ∷ # 71 ∷ # 50 ∷ # 46 ∷ # 99 ∷ # 114 ∷ # 108 ∷ # 48 ∷ # 53 ∷ # 160 ∷ # 51 ∷ # 160 ∷ # 49 ∷ # 134 ∷ # 47 ∷ # 104 ∷ # 116 ∷ # 116 ∷ # 112 ∷ # 58 ∷ # 47 ∷ # 47 ∷ # 99 ∷ # 114 ∷ # 108 ∷ # 52 ∷ # 46 ∷ # 100 ∷ # 105 ∷ # 103 ∷ # 105 ∷ # 99 ∷ # 101 ∷ # 114 ∷ # 116 ∷ # 46 ∷ # 99 ∷ # 111 ∷ # 109 ∷ # 47 ∷ # 68 ∷ # 105 ∷ # 103 ∷ # 105 ∷ # 67 ∷ # 101 ∷ # 114 ∷ # 116 ∷ # 71 ∷ # 108 ∷ # 111 ∷ # 98 ∷ # 97 ∷ # 108 ∷ # 67 ∷ # 65 ∷ # 71 ∷ # 50 ∷ # 46 ∷ # 99 ∷ # 114 ∷ [ # 108 ]

    val₃ : List Dig
    val₃ = # 4 ∷ # 116 ∷ # 48 ∷ # 114 ∷ # 48 ∷ # 55 ∷ # 160 ∷ # 53 ∷ # 160 ∷ # 51 ∷ # 134 ∷ # 49 ∷ # 104 ∷ # 116 ∷ # 116 ∷ # 112 ∷ # 58 ∷ # 47 ∷ # 47 ∷ # 99 ∷ # 114 ∷ # 108 ∷ # 52 ∷ # 46 ∷ # 100 ∷ # 105 ∷ # 103 ∷ # 105 ∷ # 99 ∷ # 101 ∷ # 114 ∷ # 116 ∷ # 46 ∷ # 99 ∷ # 111 ∷ # 109 ∷ # 47 ∷ # 68 ∷ # 105 ∷ # 103 ∷ # 105 ∷ # 67 ∷ # 101 ∷ # 114 ∷ # 116 ∷ # 71 ∷ # 108 ∷ # 111 ∷ # 98 ∷ # 97 ∷ # 108 ∷ # 82 ∷ # 111 ∷ # 111 ∷ # 116 ∷ # 71 ∷ # 50 ∷ # 46 ∷ # 99 ∷ # 114 ∷ # 108 ∷ # 48 ∷ # 55 ∷ # 160 ∷ # 53 ∷ # 160 ∷ # 51 ∷ # 134 ∷ # 49 ∷ # 104 ∷ # 116 ∷ # 116 ∷ # 112 ∷ # 58 ∷ # 47 ∷ # 47 ∷ # 99 ∷ # 114 ∷ # 108 ∷ # 51 ∷ # 46 ∷ # 100 ∷ # 105 ∷ # 103 ∷ # 105 ∷ # 99 ∷ # 101 ∷ # 114 ∷ # 116 ∷ # 46 ∷ # 99 ∷ # 111 ∷ # 109 ∷ # 47 ∷ # 68 ∷ # 105 ∷ # 103 ∷ # 105 ∷ # 67 ∷ # 101 ∷ # 114 ∷ # 116 ∷ # 71 ∷ # 108 ∷ # 111 ∷ # 98 ∷ # 97 ∷ # 108 ∷ # 82 ∷ # 111 ∷ # 111 ∷ # 116 ∷ # 71 ∷ # 50 ∷ # 46 ∷ # 99 ∷ # 114 ∷ [ # 108 ]

    test₁ : X509.CRLDistFields val₁
    test₁ = Success.value (toWitness {Q = Logging.val (runParser parseCRLDistFields val₁)} tt)

    test₂ : X509.CRLDistFields val₂
    test₂ = Success.value (toWitness {Q = Logging.val (runParser parseCRLDistFields val₂)} tt)

    test₃ : X509.CRLDistFields val₃
    test₃ = Success.value (toWitness {Q = Logging.val (runParser parseCRLDistFields val₃)} tt)
