{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.OID.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions.NonMalleable
open import Aeres.Prelude

module Aeres.Data.X690-DER.Sequence.DefinedByOID.TCB where

open Aeres.Grammar.Definitions.NonMalleable UInt8

AnyDefinedByOID : Set₁
AnyDefinedByOID = {@0 bs : List UInt8} → OID bs → @0 List UInt8 → Set

record DefinedByOIDFields (P : AnyDefinedByOID) (@0 bs : List UInt8) : Set where
  constructor mkOIDDefinedFields
  field
    @0 {o p} : List UInt8
    oid : OID o
    param  : P oid p
    @0 bs≡ : bs ≡ o ++ p

DefinedByOID : (@0 P : AnyDefinedByOID) → @0 List UInt8 → Set
DefinedByOID P = TLV Tag.Sequence (DefinedByOIDFields P)

RawDefinedByOIDFields : {P : AnyDefinedByOID} → Raw₁ RawOID P → Raw (DefinedByOIDFields P)
Raw.D (RawDefinedByOIDFields R) = Σ (Raw.D RawOID) (Raw₁.D R)
Raw.to (RawDefinedByOIDFields R) (─ _ , mkOIDDefinedFields oid param bs≡) =
  (Raw.to RawOID (─ _ , oid)) , Raw₁.to R oid (─ _ , param)
