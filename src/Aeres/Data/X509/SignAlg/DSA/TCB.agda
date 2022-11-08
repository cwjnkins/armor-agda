{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.AlgorithmIdentifier.TCB
open import Aeres.Data.X690-DER.Null.TCB
import      Aeres.Data.X509.SignAlg.TCB.OIDs as OIDs
open import Aeres.Data.X690-DER.OID.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Grammar.Definitions
open import Aeres.Prelude

module Aeres.Data.X509.SignAlg.DSA.TCB where

open Aeres.Grammar.Definitions UInt8

DSA-Like : {@0 bs : List UInt8} (o : OIDValue bs) → @0 List UInt8 → Set
DSA-Like o =
  AlgorithmIdentifier
    λ o' → Null ×ₚ const (_≋_{A = OIDValue} (TLV.val o') o)

SHA1   = DSA-Like OIDs.DSA.SHA1
SHA224 = DSA-Like OIDs.DSA.SHA224
SHA256 = DSA-Like OIDs.DSA.SHA256
