{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.EcPkAlg.Params.Curve
open import Aeres.Data.X509.EcPkAlg.Params.Properties
open import Aeres.Data.X509.EcPkAlg.Params.TCB
open import Aeres.Data.X690-DER.BitString.TCB
open import Aeres.Data.X690-DER.Int
open import Aeres.Data.X690-DER.Null
open import Aeres.Data.X690-DER.OID.TCB
open import Aeres.Data.X690-DER.OctetString.TCB
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Option
import      Aeres.Grammar.Serializer
open import Aeres.Prelude

module Aeres.Data.X509.EcPkAlg.Params.Serializer where

open Aeres.Grammar.Option     UInt8
open Aeres.Grammar.Serializer UInt8


serializeFields : Serializer EcParamsFields
serializeFields =
  serializeEquivalent Fields.equivalent
    (serialize&ₚ
      (serialize&ₚ
        (serialize&ₚ
          (serialize&ₚ
            (serialize&ₚ
              (λ where refl → self)
              (TLV.serialize id))
            (TLV.serialize Curve.serialize))
          (TLV.serialize id))
        Int.serialize)
      (Option.serialize Int.serialize))

