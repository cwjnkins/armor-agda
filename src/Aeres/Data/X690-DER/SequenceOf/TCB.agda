{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.Int
open import Aeres.Data.X690-DER.TLV
open import Aeres.Data.X690-DER.Tag
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.IList
open import Aeres.Prelude

module Aeres.Data.X690-DER.SequenceOf.TCB where

open Base256
open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.IList       UInt8

SequenceOf       = IList
SequenceOfFields = IListCons
lengthSequence   = lengthIList

pattern mkSequenceOf{bs₁}{bs₂} h t bs≡   = mkIListCons{bs₁}{bs₂} h t bs≡
pattern consSequenceOf{bs₁}{bs₂} h t bs≡ = consIList{bs₁}{bs₂} h t bs≡

BoundedSequenceOf  = IListLowerBounded
NonEmptySequenceOf = IListNonEmpty

Seq : (A : List Dig → Set) → @0 List Dig → Set
Seq A = TLV Tag.Sequence (SequenceOf A)

NonEmptySeq : (@0 A : List Dig → Set) → @0 List Dig → Set
NonEmptySeq A = TLV Tag.Sequence (NonEmptySequenceOf A)

IntegerSeq = Seq Int
