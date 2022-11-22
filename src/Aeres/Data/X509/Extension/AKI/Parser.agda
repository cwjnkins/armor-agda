{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.Extension.AKI.Properties
import      Aeres.Data.X509.Extension.AKI.TCB as AKI
open import Aeres.Data.X509.GeneralName
open import Aeres.Data.X690-DER.Int
open import Aeres.Data.X690-DER.OctetString
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parser
open import Aeres.Prelude
open import Data.List.Properties
open import Data.Nat.Properties
  hiding (_≟_)

module Aeres.Data.X509.Extension.AKI.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parser      UInt8

module parseAKIFields where
  module Here where
    AKIKeyId = "X509: Extension: AKI: key id"
    AKIAuthCertIssuer = "X509: Extension: AKI: authority key issuer"
    AKIAuthCertSN = "X509: Extension: AKI: authority certificate serial number"
    AKI = "X509: Extension: AKI"

  open AKI
  open ≡-Reasoning

  parseAKIKeyId : Parser (Logging ∘ Dec) AKIKeyId
  parseAKIKeyId = parseTLV _ Here.AKIKeyId _ parseOctetStringValue

  parseAKIAuthCertIssuer : Parser (Logging ∘ Dec) AKIAuthCertIssuer
  parseAKIAuthCertIssuer = parseTLV _ Here.AKIAuthCertIssuer _ parseGeneralNamesElems

  parseAKIAuthCertSN : Parser (Logging ∘ Dec) AKIAuthCertSN
  parseAKIAuthCertSN = parseTLV _ Here.AKIAuthCertSN _ parseIntValue

  -- NOTE: The proof effort caught a bug in my original implementation :)
  -- (Try to parse all, then check lengths)
  parseAKIFieldsSeqFields : ∀ n → Parser (Logging ∘ Dec) (ExactLength AKIFieldsSeqFields n)
  parseAKIFieldsSeqFields n =
    parseEquivalent (equivalent×ₚ equivalent)
      (parseOption₃
        TLV.nonnesting TLV.nonnesting TLV.nonnesting
        (TLV.noconfusion λ ()) (TLV.noconfusion λ ()) (TLV.noconfusion λ ())
        parseAKIKeyId parseAKIAuthCertIssuer parseAKIAuthCertSN
        (tell $ Here.AKI String.++ ": underflow") n)

  parseAKIFieldsSeq : Parser (Logging ∘ Dec) AKIFieldsSeq
  parseAKIFieldsSeq =
    parseTLV _ Here.AKI _ parseAKIFieldsSeqFields

  parseAKIFields : Parser (Logging ∘ Dec) AKIFields
  parseAKIFields =
    parseTLV _ Here.AKI _ (parseExactLength TLV.nonnesting
      (tell $ Here.AKI String.++ ": overflow") parseAKIFieldsSeq)

open parseAKIFields public using
  (parseAKIKeyId ; parseAKIAuthCertIssuer ; parseAKIAuthCertSN ; parseAKIFieldsSeqFields ; parseAKIFields)


-- private
--   module Test where

--     val₁ : List Dig
--     val₁ = # 128 ∷ # 20 ∷ # 20 ∷ # 46 ∷ # 179 ∷ # 23 ∷ # 183 ∷ # 88 ∷ # 86 ∷ # 203 ∷ # 174 ∷ # 80 ∷ # 9 ∷ # 64 ∷ # 230 ∷ # 31 ∷ # 175 ∷ # 157 ∷ # 139 ∷ # 20 ∷ # 194 ∷ [ # 198 ]

--     val₂ : List Dig
--     val₂ = # 161 ∷ # 8 ∷ # 130 ∷ # 2 ∷ # 90 ∷ # 90 ∷ # 130 ∷ # 2 ∷ # 90 ∷ [ # 90 ]
    
--     val₃ : List Dig
--     val₃ = # 130 ∷ # 2 ∷ # 2 ∷ [ # 3 ]

--     val₄ : List Dig
--     val₄ = # 4 ∷ # 24 ∷ # 48 ∷ # 22 ∷ # 128 ∷ # 20 ∷ # 138 ∷ # 116 ∷ # 127 ∷ # 175 ∷ # 133 ∷ # 205 ∷ # 238 ∷ # 149 ∷ # 205 ∷ # 61 ∷ # 156 ∷ # 208 ∷ # 226 ∷ # 70 ∷ # 20 ∷ # 243 ∷ # 113 ∷ # 53 ∷ # 29 ∷ [ # 39 ]

--     test₁ : AKIKeyId val₁
--     test₁ = Success.value (toWitness {Q = Logging.val (runParser parseAKIKeyId val₁)} tt)

--     test₂ : AKIAuthCertIssuer val₂
--     test₂ = Success.value (toWitness {Q = Logging.val (runParser parseAKIAuthCertIssuer val₂)} tt)

--     test₃ : AKIAuthCertSN val₃
--     test₃ = Success.value (toWitness {Q = Logging.val (runParser parseAKIAuthCertSN val₃)} tt)

--     test₄ : AKIFields val₄
--     test₄ = Success.value (toWitness {Q = Logging.val (runParser parseAKIFields val₄)} tt)
