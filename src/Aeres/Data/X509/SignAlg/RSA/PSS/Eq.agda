{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.HashAlg
import      Aeres.Data.X509.HashAlg.TCB.OIDs        as OIDs
open import Aeres.Data.X509.MaskGenAlg
open import Aeres.Data.X509.SignAlg.RSA.PSS.Properties
open import Aeres.Data.X509.SignAlg.RSA.PSS.TCB
import      Aeres.Data.X509.SignAlg.TCB.OIDs        as OIDs
open import Aeres.Data.X690-DER.Int
open import Aeres.Data.X690-DER.OID.TCB
open import Aeres.Data.X690-DER.OctetString
open import Aeres.Data.X690-DER.Sequence.DefinedByOID
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag                 as Tag
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
import      Aeres.Grammar.Parallel
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Seq
import      Aeres.Grammar.Sum
open import Aeres.Prelude

module Aeres.Data.X509.SignAlg.RSA.PSS.Eq where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8
open Aeres.Grammar.Parallel    UInt8
open Aeres.Grammar.Properties  UInt8
open Aeres.Grammar.Seq         UInt8
open Aeres.Grammar.Sum         UInt8

instance
  eq≋Supported : Eq≋ SupportedHashAlg
  eq≋Supported =
    Sum.sumEq≋ ⦃ eq₂ = Sum.sumEq≋ ⦃ eq₂ = Sum.sumEq≋ ⦃ eq₂ = Sum.sumEq≋ ⦄ ⦄ ⦄

  eq≋Fields : Eq≋ PSSParamFields
  eq≋Fields =
    Iso.isoEq≋ Fields.iso
      (Eq⇒Eq≋
        (Seq.eq&ₚ (Eq≋⇒Eq it)
        (Seq.eq&ₚ (Eq≋⇒Eq it)
        (Seq.eq&ₚ it (Eq≋⇒Eq (TLV.EqTLV ⦃ Option.OptionEq≋ ⦃ Parallel.eq≋Σₚ it λ a → record { _≟_ = λ x y → yes (≡-unique x y) } ⦄ ⦄))))))
  eq≋ : Eq≋ (DefinedByOIDFields PSSParam)
  eq≋ =
    DefinedByOID.eq≋
      PSSParam
      (λ o → record
        { _≋?_ = λ where
            (mk×ₚ fstₚ₁ ≋-refl) (mk×ₚ fstₚ₂ ≋-refl) →
              case fstₚ₁ ≋? fstₚ₂ ret (const _) of λ where
                (yes ≋-refl) → yes ≋-refl
                (no ¬≋) → no λ where ≋-refl → contradiction ≋-refl ¬≋
        })

