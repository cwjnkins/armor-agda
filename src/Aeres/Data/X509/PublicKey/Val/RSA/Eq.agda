{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.PublicKey.Val.RSA.Ints
open import Aeres.Data.X509.PublicKey.Val.RSA.Properties
open import Aeres.Data.X509.PublicKey.Val.RSA.TCB
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
open import Aeres.Prelude

module Aeres.Data.X509.PublicKey.Val.RSA.Eq where

open Aeres.Grammar.Definitions UInt8

instance
  eq≋ : Eq≋ RSABitStringFields
  eq≋ =
    isoEq≋ iso
      (Eq⇒Eq≋
        (eq&ₚ
          (record
            { _≟_ = λ where
              (─ _ , refl) (─ _ , refl) → yes refl })
          (Eq≋⇒Eq it)))