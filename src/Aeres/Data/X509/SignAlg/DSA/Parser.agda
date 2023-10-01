{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.SignAlg.DSA.TCB
import      Aeres.Data.X509.SignAlg.TCB.OIDs as OIDs
open import Aeres.Data.X690-DER.Null
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.Sequence.DefinedByOID
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parallel
import      Aeres.Grammar.Parser
import      Aeres.Grammar.Sum
open import Aeres.Prelude

module Aeres.Data.X509.SignAlg.DSA.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parallel    UInt8
open Aeres.Grammar.Parser      UInt8
open Aeres.Grammar.Sum         UInt8

parseDSA-Like : ∀ {@0 bs} → (o : OIDValue bs) → String → Parser (Logging ∘ Dec) (DSA-Like o)
parseDSA-Like o s =
  DefinedByOID.parse s
    λ n o' →
      parseExactLength (Parallel.nosubstrings₁ TLV.nosubstrings)
        (tell $ s String.++ ": length mismatch")
        (parse×Dec TLV.nosubstrings
          (tell $ s String.++ ": mismatched OID")
          parseNull (λ _ → _ ≋? _))
        _

parseSHA1   = parseDSA-Like OIDs.DSA.SHA1   "X509: SignAlg: DSA: SHA1"
parseSHA224 = parseDSA-Like OIDs.DSA.SHA224 "X509: SignAlg: DSA: SHA224"
parseSHA256 = parseDSA-Like OIDs.DSA.SHA256 "X509: SignAlg: DSA: SHA256"

parseSupported : Parser (Logging ∘ Dec) Supported
parseSupported =
   parseSum parseSHA1
  (parseSum parseSHA224
            parseSHA256)
