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


open parseAKIFields public using (parseAKIKeyId ; parseAKIAuthCertIssuer ; parseAKIAuthCertSN ; parseAKIFieldsSeqFields)


private
  module Test where

    AKIid₁ : List Dig
    AKIid₁ = # 128 ∷ # 20 ∷ # 20 ∷ # 46 ∷ # 179 ∷ # 23 ∷ # 183 ∷ # 88 ∷ # 86 ∷ # 203 ∷ # 174 ∷ # 80 ∷ # 9 ∷ # 64 ∷ # 230 ∷ # 31 ∷ # 175 ∷ # 157 ∷ # 139 ∷ # 20 ∷ # 194 ∷ [ # 198 ]

    AKIsn₁ : List Dig
    AKIsn₁ = # 130 ∷ # 2 ∷ # 2 ∷ [ # 3 ]

    AKIissuer₁ : List Dig
    AKIissuer₁ = # 161 ∷ # 8 ∷ # 130 ∷ # 2 ∷ # 90 ∷ # 90 ∷ # 130 ∷ # 2 ∷ # 90 ∷ [ # 90 ]

    AKIfields₁ : List Dig
    AKIfields₁ = # 130 ∷ # 2 ∷ # 2 ∷ [ # 3 ]

    test₁ : X509.AKIKeyId AKIid₁
    test₁ = Success.value (toWitness {Q = Logging.val (runParser parseAKIKeyId AKIid₁)} tt)

    test₂ : X509.AKIAuthCertIssuer AKIissuer₁
    test₂ = Success.value (toWitness {Q = Logging.val (runParser parseAKIAuthCertIssuer AKIissuer₁)} tt)

    test₃ : X509.AKIAuthCertSN AKIsn₁
    test₃ = Success.value (toWitness {Q = Logging.val (runParser parseAKIAuthCertSN AKIsn₁)} tt)

    -- AKIfieldstest₁ : X509.AKIFieldsSeqFields AKIfields₁
    -- AKIfieldstest₁ = Success.value (toWitness {Q = Logging.val (runParser {!parseAKIFieldsSeqFields!} AKIfields₁) } tt)

