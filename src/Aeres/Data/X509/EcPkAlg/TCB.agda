{-# OPTIONS --subtyping #-}

open import Aeres.Binary
import      Aeres.Data.X509.PkOID as PkOID
open import Aeres.Data.X509.EcPkAlg.Params.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Prelude

module Aeres.Data.X509.EcPkAlg.TCB where

record EcPkAlgFields (@0 bs : List UInt8) : Set where
  constructor mkEcPkAlgFields
  field
    @0 {p} : List UInt8
    oid : Singleton PkOID.EcPk
    param : EcPkAlgParams p
    @0 bs≡  : bs ≡ (Singleton.x oid) ++ p

EcPkAlg : (@0 _ : List UInt8) → Set
EcPkAlg xs = TLV Tag.Sequence EcPkAlgFields xs
