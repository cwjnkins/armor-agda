{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.PublicKey.Alg.EC.Params.Curve.TCB
open import Aeres.Data.X509.PublicKey.Alg.EC.Params.Curve.Properties
open import Aeres.Data.X690-DER.BitString
open import Aeres.Data.X690-DER.OctetString
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
import      Aeres.Grammar.Properties
open import Aeres.Prelude

module Aeres.Data.X509.PublicKey.Alg.EC.Params.Curve.Eq where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8
open Aeres.Grammar.Properties  UInt8

instance
  eq≋ : Eq≋ CurveFields
  eq≋ =
    isoEq≋ iso
      (Eq⇒Eq≋ (eq&ₚ (eq&ₚ it it) it))

  eq : Eq (Exists─ _ CurveFields)
  eq = Eq≋⇒Eq it
