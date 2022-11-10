{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.AlgorithmIdentifier
open import Aeres.Data.X509.SignAlg.DSA.TCB
open import Aeres.Data.X690-DER.Null
import      Aeres.Data.X509.SignAlg.TCB.OIDs as OIDs
open import Aeres.Data.X690-DER.OID.TCB
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
open import Aeres.Prelude

module Aeres.Data.X509.SignAlg.DSA.Properties where

open Aeres.Grammar.Definitions UInt8

@0 unambiguous : ∀ {@0 bs} → (o : OID bs) → Unambiguous (DSA-Like (TLV.val o))
unambiguous o =
  TLV.unambiguous
    (AlgorithmIdentifier.unambiguous
      _
      λ o' →
        unambiguous×ₚ
          (TLV.unambiguous (λ where refl refl → refl))
          λ where ≋-refl ≋-refl → refl)
