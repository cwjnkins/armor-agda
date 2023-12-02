open import Aeres.Binary
open import Aeres.Data.X690-DER.Int.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.IList.TCB
import      Aeres.Grammar.Parallel.TCB
open import Aeres.Prelude

module Aeres.Data.X690-DER.SequenceOf.TCB where

open Aeres.Grammar.Definitions              UInt8
open Aeres.Grammar.IList.TCB                UInt8
open Aeres.Grammar.Parallel.TCB             UInt8

-- https://www.itu.int/rec/T-REC-X.690-202102-I/en
-- 8.10.1 The encoding of a sequence-of value shall be constructed.
-- 8.10.2 The contents octets shall consist of zero, one or more complete encodings of data values from the type listed in the
-- ASN.1 definition.
-- 8.10.3 The order of the encodings of the data values shall be the same as the order of the data values in the sequence-of
-- value to be encoded.

SequenceOf       = IList
SequenceOfFields = IListCons
lengthSequence   = lengthIList

pattern mkSequenceOf{bs₁}{bs₂} h t bs≡   = mkIListCons{bs₁}{bs₂} h t bs≡
pattern consSequenceOf{bs₁}{bs₂} h t bs≡ = consIList{bs₁}{bs₂} h t bs≡

BoundedSequenceOf  = IListLowerBounded
NonEmptySequenceOf = IListNonEmpty

Seq : (A : @0 List UInt8 → Set) → @0 List UInt8 → Set
Seq A = TLV Tag.Sequence (SequenceOf A)

NonEmptySeq : (A : @0 List UInt8 → Set) → @0 List UInt8 → Set
NonEmptySeq A = TLV Tag.Sequence (NonEmptySequenceOf A)

IntegerSeq = Seq Int

RawSequenceOf : {A : @0 List UInt8 → Set} → Raw A → Raw (SequenceOf A)
Raw.D (RawSequenceOf R) = List (Raw.D R)
Raw.to (RawSequenceOf R) sq = map (λ where (─ bs , e) → Raw.to R{bs} e) (toList sq)

RawBoundedSequenceOf : ∀ {A : @0 List UInt8 → Set} → Raw A → (n : ℕ) → Raw (BoundedSequenceOf A n)
Raw.D (RawBoundedSequenceOf R n) = List (Raw.D R)
Raw.to (RawBoundedSequenceOf R n) sq = map (λ where (─ bs , e) → Raw.to R{bs} e) (toList (fstₚ sq))
