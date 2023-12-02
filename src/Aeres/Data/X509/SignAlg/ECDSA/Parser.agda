open import Aeres.Binary
open import Aeres.Data.X509.SignAlg.ECDSA.TCB
import      Aeres.Data.X509.SignAlg.TCB.OIDs as OIDs
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.Sequence.DefinedByOID
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parallel
import      Aeres.Grammar.Parser
open import Aeres.Prelude

module Aeres.Data.X509.SignAlg.ECDSA.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parallel    UInt8
open Aeres.Grammar.Parser      UInt8

private
  here' = "X509: SignAlg: ECDSA"

parseParams : ∀ n {@0 bs} → (o : OID bs) (o∈? : Dec ((-, TLV.val o) ∈ OIDs.ECDSA.Supported))
              → Parser (Logging ∘ Dec) (ExactLength (ECDSAParams' o o∈?) n)
parseParams n o (no ¬p) =
  parseExactLength (λ where _ ()) silent parseFalse n
parseParams n o (yes p) =
  parseExactLength (λ where _ (─ refl) (─ refl) → refl)
    (tell $ here' String.++ ": parameter should be absent")
    (parseErased (parseLit silent silent [])) n

parse : Parser (Logging ∘ Dec) ECDSA
parse = DefinedByOID.parse here' λ n o → parseParams n o ((-, TLV.val o) ∈? OIDs.ECDSA.Supported)
