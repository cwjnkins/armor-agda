{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.AlgorithmIdentifier
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
  eq≋ : ∀ {@0 bs} → {o : OIDValue bs} → Eq≋ (AlgorithmIdentifierFields (ECDSA-Like-Params o))
  eq≋{o = o} =
    AlgorithmIdentifier.eq≋ _
      λ o₁ →
        record
          { _≋?_ = λ where
            (mk×ₚ refl ≋-refl refl) (mk×ₚ refl ≋-refl refl) →
              yes ≋-refl
          }

  eq≋Supported : Eq≋ Supported
  eq≋Supported =
    sumEq≋ ⦃ eq₂ = sumEq≋ ⦃ eq₂ = sumEq≋ ⦃ eq₂ = sumEq≋ ⦄ ⦄ ⦄
