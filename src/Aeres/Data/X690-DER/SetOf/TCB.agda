{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.SequenceOf.TCB
open import Aeres.Data.X690-DER.SetOf.Order.TCB
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.IList.TCB
import      Aeres.Grammar.Parallel.TCB
open import Aeres.Prelude
import      Data.List.Relation.Unary.Sorted.TotalOrder

module Aeres.Data.X690-DER.SetOf.TCB where

open Aeres.Grammar.IList.TCB    UInt8
open Aeres.Grammar.Parallel.TCB UInt8

record SetOf (A : List UInt8 → Set) (@0 bs : List UInt8) : Set where
  constructor mkSetOf
  field
    elems : NonEmptySequenceOf A bs

  open Data.List.Relation.Unary.Sorted.TotalOrder bytesTotalOrder public
  elemsList = toList (fstₚ elems)

  field
    -- TODO make this T (sorted? ...)
    @0 order : Sorted (liftMapErase id (map proj₁ elemsList))
