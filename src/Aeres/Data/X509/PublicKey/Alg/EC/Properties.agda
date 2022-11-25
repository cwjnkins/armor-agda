{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.AlgorithmIdentifier
open import Aeres.Data.X509.PublicKey.Alg.EC.Params
open import Aeres.Data.X509.PublicKey.Alg.EC.TCB
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
open import Aeres.Prelude

module Aeres.Data.X509.PublicKey.Alg.EC.Properties where

open Aeres.Grammar.Definitions UInt8

@0 unambiguous : Unambiguous EC
unambiguous =
  TLV.unambiguous
    (AlgorithmIdentifier.unambiguous Params
      (λ o → unambiguous×ₚ Params.unambiguous (λ where ≋-refl ≋-refl → refl)))
