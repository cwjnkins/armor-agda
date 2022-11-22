{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.AlgorithmIdentifier
open import Aeres.Data.X509.HashAlg
import      Aeres.Data.X509.HashAlg.TCB.OIDs        as OIDs
open import Aeres.Data.X509.MaskGenAlg
open import Aeres.Data.X509.SignAlg.RSA.PSS.Properties
open import Aeres.Data.X509.SignAlg.RSA.PSS.TCB
import      Aeres.Data.X509.SignAlg.TCB.OIDs        as OIDs
open import Aeres.Data.X690-DER.Int
open import Aeres.Data.X690-DER.OID.TCB
open import Aeres.Data.X690-DER.OctetString
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag                 as Tag
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Sum
open import Aeres.Prelude

module Aeres.Data.X509.SignAlg.RSA.PSS.Eq where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8
open Aeres.Grammar.Properties  UInt8
open Aeres.Grammar.Sum         UInt8

instance
  eq≋Supported : Eq≋ SupportedHashAlg
  eq≋Supported =
    sumEq≋ ⦃ eq₂ = sumEq≋ ⦃ eq₂ = sumEq≋ ⦃ eq₂ = sumEq≋ ⦄ ⦄ ⦄

  eq≋Fields : Eq≋ PSSParamFields
  eq≋Fields =
    isoEq≋ Fields.iso
      (Eq⇒Eq≋
        (eq&ₚ (Eq≋⇒Eq it)
        (eq&ₚ (Eq≋⇒Eq it)
        (eq&ₚ it (Eq≋⇒Eq (TLV.EqTLV ⦃ Option.OptionEq≋ ⦃ eq≋Σₚ it λ a → record { _≟_ = λ x y → yes (≡-unique x y) } ⦄ ⦄))))))
  eq≋ : Eq≋ (AlgorithmIdentifierFields PSSParam)
  eq≋ =
    AlgorithmIdentifier.eq≋
      PSSParam
      (λ o → record
        { _≋?_ = λ where
            (mk×ₚ fstₚ₁ ≋-refl refl) (mk×ₚ fstₚ₂ ≋-refl refl) →
              case fstₚ₁ ≋? fstₚ₂ ret (const _) of λ where
                (yes ≋-refl) → yes ≋-refl
                (no ¬≋) → no λ where ≋-refl → contradiction ≋-refl ¬≋
        })

