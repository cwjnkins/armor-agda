{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.HashAlg.TCB
open import Aeres.Data.X509.SignAlg.TCB
import      Aeres.Data.X509.SignAlg.TCB.OIDs as OIDs
open import Aeres.Data.X509.SignAlg.ECDSA
open import Aeres.Data.X509.SignAlg.DSA
open import Aeres.Data.X509.SignAlg.Properties
open import Aeres.Data.X509.SignAlg.RSA
open import Aeres.Data.X690-DER.OctetString
open import Aeres.Data.X690-DER.Int.TCB
open import Aeres.Data.X690-DER.Null.TCB
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.OctetString.TCB
open import Aeres.Data.X690-DER.Sequence.DefinedByOID
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parallel
import      Aeres.Grammar.Sum
open import Aeres.Prelude
import      Data.List.Relation.Unary.Any.Properties as Any

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parallel    UInt8
open Aeres.Grammar.Sum         UInt8

module Aeres.Data.X509.SignAlg.Eq where

instance
  eq≋Unsupported : Eq≋ (DefinedByOIDFields UnsupportedParam)
  eq≋Unsupported =
    DefinedByOID.eq≋ UnsupportedParam
      (λ o →
        record
          { _≋?_ = λ where
            (mk×ₚ os₁ o∉₁) (mk×ₚ os₂ o∉₂) →
              case os₁ ≋? os₂ ret (const _) of λ where
                (no ¬p) → no λ where ≋-refl → contradiction ≋-refl ¬p
                (yes ≋-refl) →
                  case T-unique o∉₁ o∉₂ ret (const _) of λ where
                    refl → yes ≋-refl
          })

  eq≋ : Eq≋ SignAlg
  eq≋ = Iso.isoEq≋ iso (Sum.sumEq≋ ⦃ eq₂ = Sum.sumEq≋ ⦃ eq₂ = Sum.sumEq≋ ⦄ ⦄)
