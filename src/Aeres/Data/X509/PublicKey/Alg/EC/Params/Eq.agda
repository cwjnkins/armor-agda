{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.PublicKey.Alg.EC.Params.Curve
open import Aeres.Data.X509.PublicKey.Alg.EC.Params.Properties
open import Aeres.Data.X509.PublicKey.Alg.EC.Params.TCB
open import Aeres.Data.X690-DER.Int
open import Aeres.Data.X690-DER.Null
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.OctetString
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Sum
open import Aeres.Prelude

module Aeres.Data.X509.PublicKey.Alg.EC.Params.Eq where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8
open Aeres.Grammar.Properties  UInt8
open Aeres.Grammar.Sum         UInt8
open ≡-Reasoning

instance
  eq≋Fields : Eq≋ EcParamsFields
  eq≋Fields =
    Eq⇒Eq≋ (isoEq Fields.iso
      (eq&ₚ
        (eq&ₚ (eq&ₚ (eq&ₚ (eq&ₚ (record { _≟_ = λ where (_ , refl) (_ , refl) → yes refl }) it) it) it)
              it)
        it))

  eq≋ : Eq≋ EcPkAlgParams
  eq≋ =
    isoEq≋ iso (sumEq≋ ⦃ eq₂ = sumEq≋ ⦄)
