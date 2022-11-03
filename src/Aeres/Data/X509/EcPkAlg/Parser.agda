{-# OPTIONS --subtyping #-}

open import Aeres.Binary
import      Aeres.Data.X509.PkOID as PkOID
open import Aeres.Data.X509.EcPkAlg.Params
open import Aeres.Data.X509.EcPkAlg.Properties
open import Aeres.Data.X509.EcPkAlg.TCB
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parser
open import Aeres.Prelude

module Aeres.Data.X509.EcPkAlg.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parser      UInt8

private
  here' = "X509: EcPkAlg: parseEcPkAlgFields"

parseEcPkAlgFields : ∀ n → Parser (Logging ∘ Dec) (ExactLength EcPkAlgFields n)
parseEcPkAlgFields n =
  parseExactLength nonnesting (tell $ here' String.++ ": underflow")
    (parseEquivalent equivalent
      (parse& (λ ≡xys a₁ a₂ → trans a₁ (sym a₂))
        (parseLit
          (tell $ here' String.++ ": EcPKOID : underflow")
          (tell $ here' String.++ ": EcPKOID: mismatch")
          PkOID.EcPk)
        parseEcPkAlgParams))
    n

parseEcPkAlg :  Parser (Logging ∘ Dec) EcPkAlg
parseEcPkAlg = parseTLV _ "Ec PK Algorithm" _ parseEcPkAlgFields
