{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.PublicKey.Alg.EC.Params
open import Aeres.Data.X509.PublicKey.Alg.EC.TCB
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.Sequence.DefinedByOID
import      Aeres.Grammar.Definitions
open import Aeres.Prelude

module Aeres.Data.X509.PublicKey.Alg.EC.Eq where

open Aeres.Grammar.Definitions UInt8

instance
  eq≋ : Eq≋ (DefinedByOIDFields Params)
  eq≋ = DefinedByOID.eq≋ Params help
    where
    help : ∀ {@0 bs} → (o : OID bs) → Eq≋ (Params o)
    help o = eq≋Σₚ it λ a → record { _≟_ = λ where ≋-refl ≋-refl → yes refl }
