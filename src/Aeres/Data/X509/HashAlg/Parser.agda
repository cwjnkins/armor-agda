{-# OPTIONS --subtyping #-}

open import Aeres.Binary
import      Aeres.Data.X509.HashAlg.TCB.OIDs as OIDs
open import Aeres.Data.X509.HashAlg.TCB
open import Aeres.Data.X690-DER.Null
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.TLV
open import Aeres.Data.X690-DER.Sequence.DefinedByOID
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
import      Aeres.Grammar.Parser
import      Aeres.Grammar.Properties
open import Aeres.Prelude

module Aeres.Data.X509.HashAlg.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8
open Aeres.Grammar.Parser      UInt8
open Aeres.Grammar.Properties  UInt8

parseSHA-Like
  : ∀ {@0 bs} (o : OIDValue bs) → String → Parser (Logging ∘ Dec) (SHA-Like o)
parseSHA-Like o s =
  DefinedByOID.parse s help
  where
  help : ∀ n {@0 bs} → (o : OID bs) → Parser _ _
  help n o =
    parseEquivalent
      (Iso.symEquivalent (proj₁ (Distribute.×ₚ-Σₚ-iso{A = Option Null}{B = _}{C = _})))
      (parse×Dec exactLength-nonnesting
        (tell $ "X509: HashAlg: " String.++ s String.++ ": OID mismatch")
        (parseOption₁ExactLength TLV.nonnesting
          (tell $ "X509: HashAlg:" String.++ s String.++ ": Param: underflow")
          parseNull _)
        λ x → _ ≋? _)

parseSHA1   = parseSHA-Like OIDs.SHA1   "SHA1"
parseSHA224 = parseSHA-Like OIDs.SHA224 "SHA224"
parseSHA256 = parseSHA-Like OIDs.SHA256 "SHA256"
parseSHA384 = parseSHA-Like OIDs.SHA384 "SHA384"
parseSHA512 = parseSHA-Like OIDs.SHA512 "SHA512"
