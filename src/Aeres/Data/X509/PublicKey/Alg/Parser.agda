{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X509.PublicKey.Alg.ECPKParameters
open import Aeres.Data.X509.PublicKey.Alg.TCB
import      Aeres.Data.X509.PublicKey.Alg.TCB.OIDs as OIDs
open import Aeres.Data.X690-DER.Null
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.OctetString
open import Aeres.Data.X690-DER.Sequence.DefinedByOID
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parallel
import      Aeres.Grammar.Parser
import      Aeres.Grammar.Properties

module Aeres.Data.X509.PublicKey.Alg.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parallel    UInt8
open Aeres.Grammar.Parser      UInt8
-- open Aeres.Grammar.Properties  UInt8
-- open Aeres.Grammar.Sum         UInt8

private
  here' = "X509: PublicKey: Alg"

parseParams : ∀ n {@0 bs} → (o : OID bs) (o∈? : Dec ((-, TLV.val o) ∈ OIDs.Supported))
              → Parser (Logging ∘ Dec) (ExactLength (PKParameters' o o∈?) n)
parseParams n o (no ¬p) =
  OctetString.parseValue n
parseParams n o (yes (here px)) =
  parseExactLength TLV.nosubstrings (tell $ here' String.++ " (params): length mismatch (null)") parseNull n
parseParams n o (yes (there (here px))) =
  parseExactLength ECPKParameters.nosubstrings (tell $ here' String.++ " (params): length mismatch (EC)")
    ECPKParameters.parse n

parse : Parser (Logging ∘ Dec) PublicKeyAlg
parse = DefinedByOID.parse here' λ n o → parseParams n o ((-, TLV.val o) ∈? OIDs.Supported)
