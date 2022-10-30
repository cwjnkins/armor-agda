{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.BitString.TCB
open import Aeres.Data.X690-DER.OctetString.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Option
open import Aeres.Prelude

module Aeres.Data.X509.EcPkAlg.Params.Curve.TCB where

open Aeres.Grammar.Option UInt8

record CurveFields (@0 bs : List UInt8) : Set where
  constructor mkCurveFields
  field
    @0 {p q r} : List UInt8
    a : OctetString p
    b : OctetString q
    seed : Option BitString r
    @0 bs≡  : bs ≡ p ++ q ++ r

Curve : (@0 _ : List UInt8) → Set
Curve xs = TLV Tag.Sequence CurveFields xs

