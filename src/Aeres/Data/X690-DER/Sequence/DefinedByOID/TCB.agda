{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Prelude

module Aeres.Data.X690-DER.Sequence.DefinedByOID.TCB where

record DefinedByOIDFields
  (@0 P : {@0 bs : List UInt8} → OID bs → List UInt8 → Set) (@0 bs : List UInt8) : Set where
  constructor mkOIDDefinedFields
  field
    @0 {o p} : List UInt8
    oid : OID o
    param  : P oid p
    @0 bs≡ : bs ≡ o ++ p

DefinedByOID : (@0 P : {@0 bs : List UInt8} → OID bs → List UInt8 → Set) → @0 List UInt8 → Set
DefinedByOID P = TLV Tag.Sequence (DefinedByOIDFields P)
