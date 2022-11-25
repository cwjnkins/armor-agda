{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.AlgorithmIdentifier.TCB
open import Aeres.Data.X509.SignAlg.DSA.TCB
  using (DSA-Like)
import      Aeres.Data.X509.SignAlg.DSA.Eq as DSA
open import Aeres.Data.X509.SignAlg.ECDSA.TCB
import      Aeres.Data.X509.SignAlg.TCB.OIDs as OIDs
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.OctetString.TCB
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Sum
open import Aeres.Prelude

module Aeres.Data.X509.SignAlg.ECDSA.Eq where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Sum         UInt8

instance
  eq≋Supported : Eq≋ Supported
  eq≋Supported =
    sumEq≋ ⦃ eq₂ = sumEq≋ ⦃ eq₂ = sumEq≋ ⦃ eq₂ = sumEq≋ ⦄ ⦄ ⦄
