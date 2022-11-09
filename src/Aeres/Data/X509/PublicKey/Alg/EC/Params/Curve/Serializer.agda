{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.PublicKey.Alg.EC.Params.Curve.Properties
open import Aeres.Data.X509.PublicKey.Alg.EC.Params.Curve.TCB
open import Aeres.Data.X690-DER.BitString
open import Aeres.Data.X690-DER.OctetString.TCB
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Option
import      Aeres.Grammar.Serializer
open import Aeres.Prelude

module Aeres.Data.X509.PublicKey.Alg.EC.Params.Curve.Serializer where

open Aeres.Grammar.Option     UInt8
open Aeres.Grammar.Serializer UInt8

serialize : Serializer CurveFields
serialize =
  serializeEquivalent equivalent
    (serialize&ₚ
      (serialize&ₚ (TLV.serialize id) (TLV.serialize id))
      (Option.serialize BitString.serialize))
