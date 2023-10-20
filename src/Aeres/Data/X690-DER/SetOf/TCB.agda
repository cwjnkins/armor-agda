{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.SequenceOf.TCB
open import Aeres.Data.X690-DER.SetOf.Order.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions.NonMalleable
import      Aeres.Grammar.IList.TCB
import      Aeres.Grammar.Parallel.TCB
open import Aeres.Prelude
import      Data.List.Relation.Unary.Sorted.TotalOrder

module Aeres.Data.X690-DER.SetOf.TCB where

open Aeres.Grammar.Definitions.NonMalleable UInt8
open Aeres.Grammar.IList.TCB                UInt8
open Aeres.Grammar.Parallel.TCB             UInt8

record SetOfFields (A : @0 List UInt8 → Set) (@0 bs : List UInt8) : Set where
  constructor mkSetOfFields
  field
    elems : NonEmptySequenceOf A bs

  open Data.List.Relation.Unary.Sorted.TotalOrder bytesTotalOrder
  @0 orderingList : List (List UInt8)
  orderingList = liftMapErase{A = Exists─ _ A} proj₁ (toList (fstₚ elems))

  field
    @0 order : True (sorted? _≲?_ orderingList)

SetOf : (A : @0 List UInt8 → Set) → @0 List UInt8 → Set
SetOf A = TLV Tag.Sett (SetOfFields A)

RawSetOfFields : {A : @0 List UInt8 → Set} → Raw A → Raw (SetOfFields A)
Raw.D (RawSetOfFields R) = Raw.D (RawBoundedSequenceOf R 1)
Raw.to (RawSetOfFields R) so = Raw.to (RawBoundedSequenceOf R 1) (SetOfFields.elems so)

RawSetOf : {A : @0 List UInt8 → Set} → Raw A → Raw (SetOf A)
RawSetOf R = RawTLV _ (RawSetOfFields R)
