open import Aeres.Binary
open import Aeres.Data.X509.HashAlg.RFC4055.Properties
open import Aeres.Data.X509.HashAlg.RFC4055.TCB
import      Aeres.Data.X509.HashAlg.TCB.OIDs as OIDs
open import Aeres.Data.X690-DER.Null
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.Sequence.DefinedByOID
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
import      Aeres.Grammar.Parallel
import      Aeres.Grammar.Parser
open import Aeres.Prelude

module Aeres.Data.X509.HashAlg.RFC4055.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8
open Aeres.Grammar.Parallel    UInt8
open Aeres.Grammar.Parser      UInt8

private
  here' = "X509: HashAlg: RFC4055"

parseParam : ∀ n {@0 bs : List UInt8} → (o : OID bs) → (o∈? : Dec ((-, TLV.val o) ∈ OIDs.RFC4055))
             → Parser (Logging ∘ Dec) (ExactLength (HashAlgParam' o o∈?) n)
parseParam n o (no ¬p) =
  parseExactLength (λ where _ ()) silent parseFalse n
parseParam n o (yes p) =
  Option.parseOption₁ExactLength
    TLV.nosubstrings
    (tell $ here' String.++ " (param): underflow")
    Null.parse n

parse : Parser (Logging ∘ Dec) HashAlg
parse = DefinedByOID.parse here' λ n o → parseParam n o ((-, TLV.val o) ∈? OIDs.RFC4055)
