{-# OPTIONS --subtyping #-}

open import Aeres.Binary
import      Aeres.Data.X509.Extension.AIA.AccessDesc.TCB.OIDs as OIDs
open import Aeres.Data.X509.Extension.AIA.AccessDesc.TCB
open import Aeres.Data.X509.GeneralName
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.Sequence.DefinedByOID
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parallel
import      Aeres.Grammar.Parser
open import Aeres.Prelude

module Aeres.Data.X509.Extension.AIA.AccessDesc.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parallel    UInt8
open Aeres.Grammar.Parser      UInt8

private
  here' = "X509: Extension: AIA: AccessDesc:"

parseAccessDesc : Parser (Logging ∘ Dec) AccessDesc
parseAccessDesc =
  DefinedByOID.parse here'
    λ n o →
      parseExactLength (Parallel.nosubstrings₁ GeneralName.nosubstrings)
        (tell $ here' String.++ ": length mismatch")
        (parse×Dec GeneralName.nosubstrings
          (tell $ here' String.++ ": unknonwn OID")
          parseGeneralName
          λ x → T-dec)
        n
