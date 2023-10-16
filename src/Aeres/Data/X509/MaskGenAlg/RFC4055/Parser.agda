{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.HashAlg.RFC4055
import      Aeres.Data.X509.MaskGenAlg.TCB.OIDs as OIDs
open import Aeres.Data.X509.MaskGenAlg.RFC4055.Properties
open import Aeres.Data.X509.MaskGenAlg.RFC4055.TCB
open import Aeres.Data.X690-DER.Null
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.Sequence.DefinedByOID
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parallel
import      Aeres.Grammar.Parser
open import Aeres.Prelude

module Aeres.Data.X509.MaskGenAlg.RFC4055.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parallel    UInt8
open Aeres.Grammar.Parser      UInt8

private
  here' = "X509: Data: MaskGenAlg: RFC4055"

parseParam : ∀ n {@0 bs} → (o : OID bs) (o∈? : Dec (_≋_{A = OIDValue} (TLV.val o) OIDs.MGF1))
             → Parser (Logging ∘ Dec) (ExactLength (MGF1Params' o o∈?) n)
parseParam n o (no ¬p) = parseExactLength (λ where _ ()) silent parseFalse _
parseParam n o (yes p) =
  parseExactLength TLV.nosubstrings (tell $ here' String.++ " (params): length mismatch")
    RFC4055.parse n

parse : Parser (Logging ∘ Dec) MGF1
parse = DefinedByOID.parse here' λ n o → parseParam n o ((TLV.val o) ≋? OIDs.MGF1)
