{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Decidable.GeneralName
open import Aeres.Data.X509.Decidable.Octetstring
open import Aeres.Data.X509.Decidable.Seq
open import Aeres.Data.X509.Decidable.TLV
open import Aeres.Data.X509.Properties as Props
open import Aeres.Grammar.Definitions
open import Aeres.Grammar.Parser
open import Data.List.Properties
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Decidable.AIAFields where

open Base256

module parseAIAFields where
  here' = "parseAIAFields"

  open ≡-Reasoning


  parseAccessMethod : Parser Dig (Logging ∘ Dec) X509.AccessMethod
  runParser parseAccessMethod xs = do
    no ¬parse₁ ← runParser (parseLit _ (tell $ here' String.++ ": underflow") (tell $ here' String.++ ": mismatched CA Issuer ID") X509.ACMOID.CAISSUERS) xs  
      where yes x → return (yes (mapSuccess _ (λ {xs} eq → X509.caissid {xs} eq) x) )
    no ¬parse₂ ← runParser (parseLit _ (tell $ here' String.++ ": underflow") (tell $ here' String.++ ": mismatched OCSP ID") X509.ACMOID.OCSP) xs 
      where yes x → return (yes (mapSuccess _ (λ {xs} eq → X509.ocspid {xs} eq) x))
    return ∘ no $ λ where
      (success prefix read read≡ (X509.caissid x) suffix ps≡) → contradiction (success _ _ read≡ x _ ps≡) ¬parse₁
      (success prefix read read≡ (X509.ocspid x) suffix ps≡) → contradiction (success _ _ read≡ x _ ps≡) ¬parse₂

  parseAccessDescFields : ∀ n → Parser Dig (Logging ∘ Dec) (ExactLength _ X509.AccessDescFields n)
  parseAccessDescFields n = parseExactLength _  Props.AccessDescFields.nonnesting (tell $ here' String.++ ": underflow")
    (parseEquivalent _ Props.AccessDescFields.equivalent (parse& _ Props.AccessMethod.nonnesting parseAccessMethod parseGeneralName)) n

  parseAccessDesc :  Parser Dig (Logging ∘ Dec) X509.AccessDesc
  parseAccessDesc = parseTLV _ "Access Description" _ parseAccessDescFields

  parseAIAFields : Parser Dig (Logging ∘ Dec) X509.AIAFields
  parseAIAFields = parseTLV _ "AIA Fields" _ (parseExactLength _ Props.TLV.nonnesting (tell $ here' String.++ ": underflow")
                     (parseSeq "AIA Fields Elems" _ Props.TLV.nonempty Props.TLV.nonnesting parseAccessDesc) )

open parseAIAFields public using (parseAIAFields)


private
  module Test where

    val₁ : List Dig
    val₁ = # 4 ∷ # 94 ∷ # 48 ∷ # 92 ∷ # 48 ∷ # 39 ∷ # 6 ∷ # 8 ∷ # 43 ∷ # 6 ∷ # 1 ∷ # 5 ∷ # 5 ∷ # 7 ∷ # 48 ∷ # 1 ∷ # 134 ∷ # 27 ∷ # 104 ∷ # 116 ∷ # 116 ∷ # 112 ∷ # 58 ∷ # 47 ∷ # 47 ∷ # 111 ∷ # 99 ∷ # 115 ∷ # 112 ∷ # 46 ∷ # 112 ∷ # 107 ∷ # 105 ∷ # 46 ∷ # 103 ∷ # 111 ∷ # 111 ∷ # 103 ∷ # 47 ∷ # 103 ∷ # 116 ∷ # 115 ∷ # 49 ∷ # 99 ∷ # 51 ∷ # 48 ∷ # 49 ∷ # 6 ∷ # 8 ∷ # 43 ∷ # 6 ∷ # 1 ∷ # 5 ∷ # 5 ∷ # 7 ∷ # 48 ∷ # 2 ∷ # 134 ∷ # 37 ∷ # 104 ∷ # 116 ∷ # 116 ∷ # 112 ∷ # 58 ∷ # 47 ∷ # 47 ∷ # 112 ∷ # 107 ∷ # 105 ∷ # 46 ∷ # 103 ∷ # 111 ∷ # 111 ∷ # 103 ∷ # 47 ∷ # 114 ∷ # 101 ∷ # 112 ∷ # 111 ∷ # 47 ∷ # 99 ∷ # 101 ∷ # 114 ∷ # 116 ∷ # 115 ∷ # 47 ∷ # 103 ∷ # 116 ∷ # 115 ∷ # 49 ∷ # 99 ∷ # 51 ∷ # 46 ∷ # 100 ∷ # 101 ∷ [ # 114 ]

    val₂ : List Dig
    val₂ = # 4 ∷ # 104 ∷ # 48 ∷ # 102 ∷ # 48 ∷ # 36 ∷ # 6 ∷ # 8 ∷ # 43 ∷ # 6 ∷ # 1 ∷ # 5 ∷ # 5 ∷ # 7 ∷ # 48 ∷ # 1 ∷ # 134 ∷ # 24 ∷ # 104 ∷ # 116 ∷ # 116 ∷ # 112 ∷ # 58 ∷ # 47 ∷ # 47 ∷ # 111 ∷ # 99 ∷ # 115 ∷ # 112 ∷ # 46 ∷ # 100 ∷ # 105 ∷ # 103 ∷ # 105 ∷ # 99 ∷ # 101 ∷ # 114 ∷ # 116 ∷ # 46 ∷ # 99 ∷ # 111 ∷ # 109 ∷ # 48 ∷ # 62 ∷ # 6 ∷ # 8 ∷ # 43 ∷ # 6 ∷ # 1 ∷ # 5 ∷ # 5 ∷ # 7 ∷ # 48 ∷ # 2 ∷ # 134 ∷ # 50 ∷ # 104 ∷ # 116 ∷ # 116 ∷ # 112 ∷ # 58 ∷ # 47 ∷ # 47 ∷ # 99 ∷ # 97 ∷ # 99 ∷ # 101 ∷ # 114 ∷ # 116 ∷ # 115 ∷ # 46 ∷ # 100 ∷ # 105 ∷ # 103 ∷ # 105 ∷ # 99 ∷ # 101 ∷ # 114 ∷ # 116 ∷ # 46 ∷ # 99 ∷ # 111 ∷ # 109 ∷ # 47 ∷ # 68 ∷ # 105 ∷ # 103 ∷ # 105 ∷ # 67 ∷ # 101 ∷ # 114 ∷ # 116 ∷ # 71 ∷ # 108 ∷ # 111 ∷ # 98 ∷ # 97 ∷ # 108 ∷ # 67 ∷ # 65 ∷ # 71 ∷ # 50 ∷ # 46 ∷ # 99 ∷ # 114 ∷ [  # 116 ]

    test₁ : X509.AIAFields val₁
    test₁ = Success.value (toWitness {Q = Logging.val (runParser parseAIAFields val₁)} tt)

    test₂ : X509.AIAFields val₂
    test₂ = Success.value (toWitness {Q = Logging.val (runParser parseAIAFields val₂)} tt)
