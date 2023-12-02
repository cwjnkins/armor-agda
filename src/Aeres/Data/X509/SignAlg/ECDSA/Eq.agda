open import Aeres.Binary
open import Aeres.Data.X509.SignAlg.ECDSA.TCB
import      Aeres.Data.X509.SignAlg.TCB.OIDs as OIDs
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.Sequence.DefinedByOID
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
open import Aeres.Prelude

module Aeres.Data.X509.SignAlg.ECDSA.Eq where

open Aeres.Grammar.Definitions UInt8

instance
  eq≋ : Eq≋ (DefinedByOIDFields ECDSAParams)
  eq≋ = DefinedByOID.eq≋ ECDSAParams λ o →
          case (-, TLV.val o) ∈? OIDs.ECDSA.Supported
          ret (λ o∈? → Eq≋ (ECDSAParams' o o∈?))
          of λ where
            (no ¬p) → record { _≋?_ = λ () }
            (yes p) → record { _≋?_ = λ where (─ refl) (─ refl) → yes ≋-refl }
