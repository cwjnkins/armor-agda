{-# OPTIONS --subtyping #-}

open import Aeres.Binary
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Data.X690-DER.OID
import      Aeres.Grammar.Parallel.TCB
import      Aeres.Grammar.Parser
open import Aeres.Prelude

module Aeres.Data.X509.PublicKey.Alg.TCB.OIDs where

open Aeres.Grammar.Parallel.TCB UInt8
open Aeres.Grammar.Parser       UInt8

RSALit : List UInt8
RSALit = # 42 ∷ # 134 ∷ # 72 ∷ # 134 ∷ # 247 ∷ # 13 ∷ # 1 ∷ # 1 ∷ [ # 1 ]

RSA : OIDValue RSALit
RSA = fstₚ (Success.value (toWitness{Q = Logging.val (runParser (parseOIDValue (length RSALit)) RSALit)} tt))

ECLit : List UInt8
ECLit = # 42 ∷ # 134 ∷ # 72 ∷ # 206 ∷ # 61 ∷ # 2 ∷ [ # 1 ]

EC : OIDValue ECLit
EC = fstₚ (Success.value (toWitness{Q = Logging.val (runParser (parseOIDValue (length ECLit)) ECLit)} tt))
