{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.GeneralNames
open import Aeres.Data.X509.Extension.CRLDistPoint.DistPoint.Name
open import Aeres.Data.X509.Extension.CRLDistPoint.DistPoint.Properties
open import Aeres.Data.X509.Extension.CRLDistPoint.DistPoint.TCB
open import Aeres.Data.X690-DER.BitString
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
import      Aeres.Grammar.Parallel
import      Aeres.Grammar.Parser
import      Aeres.Grammar.Properties
open import Aeres.Prelude

module Aeres.Data.X509.Extension.CRLDistPoint.DistPoint.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8
open Aeres.Grammar.Parallel    UInt8
open Aeres.Grammar.Parser      UInt8
open Aeres.Grammar.Properties  UInt8

private
  here' = "X509: Extension: CRLDistPoint: DistPoint"

parseDistPointFields : ∀ n → Parser (Logging ∘ Dec) (ExactLength DistPointFields n)
parseDistPointFields n =
  parseEquivalent
    (Parallel.equivalent₁ equivalentDistPointFields)
    (Option.parseOption₃ TLV.nosubstrings TLV.nosubstrings TLV.nosubstrings
      (TLV.noconfusion (λ where ())) (TLV.noconfusion (λ where ())) (TLV.noconfusion (λ where ()))
      (parseTLV Tag.AA0 (here' String.++ ": name") DistPointNameChoice
        (parseExactLength Name.nosubstrings
          (tell $ here' String.++ ": underflow (Name)")
          parseDistPointNameChoice))
      (parseTLV Tag.A81 "reason flags" _ parseBitstringValue)
      (parseTLV Tag.AA2 "CRL issuer" GeneralNamesElems
        parseGeneralNamesElems)
      (tell $ here' String.++ ": failed")
      n)

parseDistPoint : Parser (Logging ∘ Dec) DistPoint
parseDistPoint =
  parseTLV _ here' _ parseDistPointFields
