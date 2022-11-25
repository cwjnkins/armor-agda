{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.PublicKey.Alg.EC.Params.Curve.TCB
open import Aeres.Data.X690-DER.BitString.TCB
open import Aeres.Data.X690-DER.Int.TCB
open import Aeres.Data.X690-DER.Null
open import Aeres.Data.X690-DER.OID.TCB
open import Aeres.Data.X690-DER.OctetString.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Option
open import Aeres.Prelude

module Aeres.Data.X509.PublicKey.Alg.EC.Params.TCB where

open Aeres.Grammar.Option UInt8

FieldID : (@0 _ : List UInt8) → Set
FieldID xs = TLV Tag.Sequence OctetStringValue xs

record EcParamsFields (@0 bs : List UInt8) : Set where
  constructor mkEcParamsFields
  field
    @0 {f c b o cf} : List UInt8
    version : Singleton (# 2 ∷ # 1 ∷ [ # 1 ])
    fieldID : FieldID f
    curve : Curve c
    base : OctetString b
    order : Int o
    cofactor : Option Int cf
    @0 bs≡  : bs ≡ Singleton.x version ++ f ++ c ++ b ++ o ++ cf

EcParams : (@0 _ : List UInt8) → Set
EcParams xs = TLV Tag.Sequence EcParamsFields xs

data EcPkAlgParams : @0 List UInt8 → Set where
  ecparams : ∀ {@0 bs} → EcParams bs → EcPkAlgParams bs
  namedcurve : ∀ {@0 bs} → OID bs → EcPkAlgParams bs
  implicitlyCA : ∀ {@0 bs} → Null bs → EcPkAlgParams bs
