{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.PublicKey.Val.RSA.Ints.Properties
open import Aeres.Data.X509.PublicKey.Val.RSA.Ints.TCB
import      Aeres.Grammar.Definitions
open import Aeres.Data.X690-DER.Int
open import Aeres.Data.X690-DER.OctetString
open import Aeres.Data.X690-DER.TLV
open import Aeres.Prelude

module Aeres.Data.X509.PublicKey.Val.RSA.Ints.Eq where

open Aeres.Grammar.Definitions UInt8

instance
  eq≋ : Eq≋ RSAPkIntsFields
  eq≋ =
    isoEq≋ iso (Eq⇒Eq≋ (eq&ₚ it it))
