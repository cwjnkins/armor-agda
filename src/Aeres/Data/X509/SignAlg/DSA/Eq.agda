{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.SignAlg.DSA.TCB
open import Aeres.Data.X690-DER.Null.TCB
import      Aeres.Data.X509.SignAlg.TCB.OIDs as OIDs
open import Aeres.Data.X690-DER.Null
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.OctetString.TCB
open import Aeres.Data.X690-DER.Sequence.DefinedByOID
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Sum
open import Aeres.Prelude

module Aeres.Data.X509.SignAlg.DSA.Eq where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Sum         UInt8

instance
  eq≋ : ∀ {@0 bs} → {o : OIDValue bs} → Eq≋ (DefinedByOIDFields (DSA-Like-Params o))
  eq≋{o = o} =
    DefinedByOID.eq≋ (DSA-Like-Params o)
      λ o₁ →
        record
          { _≋?_ = λ where
            (mk×ₚ n ≋-refl refl) (mk×ₚ n' ≋-refl refl) →
              case n ≋? n' ret (const _) of λ where
                (no ¬p) → no λ where ≋-refl → contradiction ≋-refl ¬p
                (yes ≋-refl) → yes ≋-refl
          }

  eq≋Supported : Eq≋ Supported
  eq≋Supported =
    sumEq≋ ⦃ eq₂ = sumEq≋ ⦄
