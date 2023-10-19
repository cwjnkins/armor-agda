{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.HashAlg.RFC4055.TCB
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
  eq≋ : Eq≋ (DefinedByOIDFields SignAlgParam)
  eq≋ =
    DefinedByOID.eq≋ SignAlgParam
      λ o →
        case isSupported o
        ret (λ o∈? → Eq≋ (SignAlgParam' o o∈?))
        of λ where
          (no ¬p) → it
          (yes p) →
            case lookupSignAlg o p
            ret (λ o∈ → Eq≋ (SignAlgParam“ o o∈))
            of λ where
              (inj₁ x) → record { _≋?_ = λ { (─ refl) (─ refl) → yes ≋-refl } }
              (inj₂ (inj₁ x)) → record { _≋?_ = λ { (─ refl) (─ refl) → yes ≋-refl } }
              (inj₂ (inj₂ y)) → RSA.eq≋Params'{o = o}{y}

  eq : Eq (Exists─ _ (DefinedByOIDFields SignAlgParam))
  eq = Eq≋⇒Eq it
