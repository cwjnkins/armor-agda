{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Decidable.GeneralName
open import Aeres.Data.X509.Decidable.Int
open import Aeres.Data.X509.Decidable.Length
open import Aeres.Data.X509.Decidable.Octetstring
open import Aeres.Data.X509.Decidable.TLV
open import Aeres.Data.X509.Properties as Props
open import Aeres.Grammar.Definitions
open import Aeres.Grammar.Parser
open import Data.List.Properties
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Decidable.AKIFields where

open Base256

module parseAKIFields where
  module Here where
    AKIKeyId = "AKI key id"
    AKIAuthCertIssuer = "AKI auth. cert. issuer"
    AKIAuthCertSN = "AKI auth. cert. SN"
    AKI = "AKI"

  open ≡-Reasoning

  parseAKIKeyId : Parser Dig (Logging ∘ Dec) X509.AKIKeyId
  parseAKIKeyId = parseTLV _ Here.AKIKeyId _ parseOctetstringValue

  parseAKIAuthCertIssuer : Parser Dig (Logging ∘ Dec) X509.AKIAuthCertIssuer
  parseAKIAuthCertIssuer = parseTLV _ Here.AKIAuthCertIssuer _ parseGeneralNamesElems

  parseAKIAuthCertSN : Parser Dig (Logging ∘ Dec) X509.AKIAuthCertSN
  parseAKIAuthCertSN = parseTLV _ Here.AKIAuthCertSN _ parseIntValue

  -- NOTE: The proof effort caught a bug in my original implementation :)
  -- (Try to parse all, then check lengths)
  parseAKIFieldsSeqFields : ∀ n → Parser Dig (Logging ∘ Dec) (ExactLength _ X509.AKIFieldsSeqFields n)
  parseAKIFieldsSeqFields n =
    parseEquivalent _ (equivalent×ₚ _ Props.AKIFieldsSeqFields.equivalent)
      (parseOption₃ _
        Props.TLV.nonnesting Props.TLV.nonnesting Props.TLV.nonnesting
        (TLV.noconfusion λ ()) (Props.TLV.noconfusion λ ()) (Props.TLV.noconfusion λ ())
        parseAKIKeyId parseAKIAuthCertIssuer parseAKIAuthCertSN
        (tell $ Here.AKI String.++ ": underflow") n)

  parseAKIFieldsSeq : Parser _ (Logging ∘ Dec) X509.AKIFieldsSeq
  parseAKIFieldsSeq =
    parseTLV _ Here.AKI _ parseAKIFieldsSeqFields

  parseAKIFields : Parser _ (Logging ∘ Dec) X509.AKIFields
  parseAKIFields =
    parseTLV _ Here.AKI _ (parseExactLength _ Props.TLV.nonnesting
      (tell $ Here.AKI String.++ ": overflow") parseAKIFieldsSeq)

open parseAKIFields public using
  (parseAKIKeyId ; parseAKIAuthCertIssuer ; parseAKIAuthCertSN ; parseAKIFieldsSeqFields ; parseAKIFields)


private
  module Test where

    val₁ : List Dig
    val₁ = # 128 ∷ # 20 ∷ # 20 ∷ # 46 ∷ # 179 ∷ # 23 ∷ # 183 ∷ # 88 ∷ # 86 ∷ # 203 ∷ # 174 ∷ # 80 ∷ # 9 ∷ # 64 ∷ # 230 ∷ # 31 ∷ # 175 ∷ # 157 ∷ # 139 ∷ # 20 ∷ # 194 ∷ [ # 198 ]

    val₂ : List Dig
    val₂ = # 161 ∷ # 8 ∷ # 130 ∷ # 2 ∷ # 90 ∷ # 90 ∷ # 130 ∷ # 2 ∷ # 90 ∷ [ # 90 ]
    
    val₃ : List Dig
    val₃ = # 130 ∷ # 2 ∷ # 2 ∷ [ # 3 ]

    val₄ : List Dig
    val₄ = # 4 ∷ # 24 ∷ # 48 ∷ # 22 ∷ # 128 ∷ # 20 ∷ # 138 ∷ # 116 ∷ # 127 ∷ # 175 ∷ # 133 ∷ # 205 ∷ # 238 ∷ # 149 ∷ # 205 ∷ # 61 ∷ # 156 ∷ # 208 ∷ # 226 ∷ # 70 ∷ # 20 ∷ # 243 ∷ # 113 ∷ # 53 ∷ # 29 ∷ [ # 39 ]

    test₁ : X509.AKIKeyId val₁
    test₁ = Success.value (toWitness {Q = Logging.val (runParser parseAKIKeyId val₁)} tt)

    test₂ : X509.AKIAuthCertIssuer val₂
    test₂ = Success.value (toWitness {Q = Logging.val (runParser parseAKIAuthCertIssuer val₂)} tt)

    test₃ : X509.AKIAuthCertSN val₃
    test₃ = Success.value (toWitness {Q = Logging.val (runParser parseAKIAuthCertSN val₃)} tt)

    test₄ : X509.AKIFields val₄
    test₄ = Success.value (toWitness {Q = Logging.val (runParser parseAKIFields val₄)} tt)
