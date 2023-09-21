{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.PublicKey.Alg.TCB
open import Aeres.Data.X509.PublicKey.Alg.EC
open import Aeres.Data.X509.PublicKey.Alg.RSA
open import Aeres.Data.X509.SignAlg.DSA
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.OctetString
open import Aeres.Data.X690-DER.Sequence.DefinedByOID
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Sum
open import Aeres.Prelude

module Aeres.Data.X509.PublicKey.Alg.Eq where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Sum         UInt8

instance
  eq≋Unsupported : Eq≋ (DefinedByOIDFields UnsupportedParam)
  eq≋Unsupported = DefinedByOID.eq≋ UnsupportedParam help
    where
    help : ∀ {@0 bs} → (o : OID bs) → Eq≋ (UnsupportedParam o)
    help o = eq≋Σₚ it λ _ → record { _≟_ = λ x y → yes (T-unique x y) }

  eq≋ : Eq≋ PublicKeyAlg
  eq≋ =
    sumEq≋ ⦃ eq₂ = sumEq≋  ⦄
