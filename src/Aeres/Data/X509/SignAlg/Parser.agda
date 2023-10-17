{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X509.SignAlg.DSA
open import Aeres.Data.X509.SignAlg.ECDSA
open import Aeres.Data.X509.SignAlg.Properties
open import Aeres.Data.X509.SignAlg.RSA
open import Aeres.Data.X509.SignAlg.TCB
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.OctetString
open import Aeres.Data.X690-DER.Sequence.DefinedByOID
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parallel
import      Aeres.Grammar.Parser
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Sum

module Aeres.Data.X509.SignAlg.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parallel    UInt8
open Aeres.Grammar.Parser      UInt8
open Aeres.Grammar.Properties  UInt8
open Aeres.Grammar.Sum         UInt8

private
  here' = "X509: SignAlg"

parseSignAlg : Parser (Logging ∘ Dec) SignAlg
parseSignAlg = parseTLV _ (here' String.++ ": unsupported") _
    (parseExactLength (DefinedByOID.nosubstrings _ nosubstringsParam)
      (tell $ here' String.++ ": underflow parsing parameter") pp)
  where
  pp : Parser (Logging ∘ Dec) (DefinedByOIDFields SignAlgParam)
  pp = parseEquivalent
         equivalent
         (parseSum DSA.parse
         (parseSum ECDSA.parse
                   RSA.parse))
