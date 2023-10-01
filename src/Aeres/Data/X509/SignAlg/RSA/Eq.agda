{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.TLV
open import Aeres.Data.X509.SignAlg.RSA.PSS
open import Aeres.Data.X509.SignAlg.RSA.TCB
open import Aeres.Data.X509.HashAlg
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Sum
open import Aeres.Prelude

module Aeres.Data.X509.SignAlg.RSA.Eq where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Sum         UInt8

instance
  eq≋Supported : Eq≋ Supported
  eq≋Supported =
    Sum.sumEq≋ ⦃ eq₂ = Sum.sumEq≋ ⦃ eq₂ = Sum.sumEq≋ ⦃ eq₂ = Sum.sumEq≋ ⦃ eq₂ =
    Sum.sumEq≋ ⦃ eq₂ = Sum.sumEq≋ ⦃ eq₂ = Sum.sumEq≋ ⦄ ⦄ ⦄ ⦄ ⦄ ⦄
