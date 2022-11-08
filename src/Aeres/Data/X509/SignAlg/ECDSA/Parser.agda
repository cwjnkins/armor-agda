{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.AlgorithmIdentifier
open import Aeres.Data.X509.SignAlg.DSA.Parser
  using (parseDSA-Like)
open import Aeres.Data.X509.SignAlg.ECDSA.TCB
import      Aeres.Data.X509.SignAlg.TCB.OIDs as OIDs
open import Aeres.Data.X690-DER.Null
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parser
open import Aeres.Prelude

module Aeres.Data.X509.SignAlg.ECDSA.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parser      UInt8

parseSHA1   = parseDSA-Like OIDs.ECDSA.SHA1   "X509: SignAlg: ECDSA: SHA1"
parseSHA224 = parseDSA-Like OIDs.ECDSA.SHA224 "X509: SignAlg: ECDSA: SHA224"
parseSHA256 = parseDSA-Like OIDs.ECDSA.SHA256 "X509: SignAlg: ECDSA: SHA256"
