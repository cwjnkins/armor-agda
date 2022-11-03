{-# OPTIONS --subtyping #-}

open import Aeres.Binary
import      Aeres.Data.X509.PkOID       as PkOID
open import Aeres.Data.X509.RSAPkAlg.Properties
open import Aeres.Data.X509.RSAPkAlg.TCB
open import Aeres.Data.X690-DER.Null
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag     as Tag
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parser
open import Aeres.Prelude

module Aeres.Data.X509.RSAPkAlg.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parser      UInt8

private
  here' = "X509: RSAPkAlg: parseRSAPkAlgFields"

parseRSAPkAlgFields : ∀ n → Parser (Logging ∘ Dec) (ExactLength RSAPkAlgFields n)
parseRSAPkAlgFields n =
  parseExactLength nonnesting (tell $ here' String.++ ": underflow")
    (parseEquivalent equivalent
      (parse& (λ ≡xys a₁ a₂ → trans a₁ (sym a₂))
        (parseLit (tell $ here' String.++ ": RSAPKOID : underflow") (tell $ here' String.++ ": RSAPKOID: mismatch") PkOID.RsaEncPk)
        parseNull))
    n

parseRSAPkAlg :  Parser (Logging ∘ Dec) RSAPkAlg
parseRSAPkAlg = parseTLV _ "RSA PK Algorithm" _ parseRSAPkAlgFields
