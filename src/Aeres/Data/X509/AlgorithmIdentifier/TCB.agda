{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Prelude

module Aeres.Data.X509.AlgorithmIdentifier.TCB where

record AlgorithmIdentifierFields
  (@0 P : {@0 bs : List UInt8} → OID bs → List UInt8 → Set) (@0 bs : List UInt8) : Set where
  constructor mkAlgIDFields
  field
    @0 {o p} : List UInt8
    algOID : OID o
    param  : P algOID p
    @0 bs≡ : bs ≡ o ++ p

AlgorithmIdentifier : (@0 P : {@0 bs : List UInt8} → OID bs → List UInt8 → Set) → @0 List UInt8 → Set
AlgorithmIdentifier P = TLV Tag.Sequence (AlgorithmIdentifierFields P)
