{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
-- import      Aeres.Grammar.Definitions
-- import      Aeres.Grammar.Option
open import Aeres.Prelude

-- open Aeres.Grammar.Definitions UInt8
-- open Aeres.Grammar.Option      UInt8

module Aeres.Data.X509.AlgorithmIdentifier.TCB where

record AlgorithmIdentifierFields
  (P : {@0 bs : List UInt8} → OID bs → @0 List UInt8 → Set) (@0 bs : List UInt8) : Set where
  constructor mkAlgIDFields
  field
    @0 {o p} : List UInt8
    algOID : OID o
    param  : P algOID p
    @0 bs≡ : bs ≡ o ++ p

AlgorithmIdentifier : (P : {@0 bs : List UInt8} → OID bs → @0 List UInt8 → Set) → @0 List UInt8 → Set
AlgorithmIdentifier P = TLV Tag.Sequence (AlgorithmIdentifierFields P)
