{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.PublicKey.Alg.ECPKParameters.ECParameters
open import Aeres.Data.X509.PublicKey.Alg.ECPKParameters.Properties
open import Aeres.Data.X509.PublicKey.Alg.ECPKParameters.TCB
open import Aeres.Data.X690-DER.Null as Null
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parser
import      Aeres.Grammar.Sum
open import Aeres.Prelude

module Aeres.Data.X509.PublicKey.Alg.ECPKParameters.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parser      UInt8
open Aeres.Grammar.Sum         UInt8

parse : Parser (Logging ∘ Dec) ECPKParameters
parse = parseEquivalent equivalent (parseSum ECParameters.parse (parseSum parseOID Null.parse))
