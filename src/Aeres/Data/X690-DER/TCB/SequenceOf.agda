{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.TCB.TLV
import      Aeres.Data.X690-DER.TCB.Tag as Tag
import      Aeres.Grammar.Definitions
open import Aeres.Prelude

module Aeres.Data.X690-DER.TCB.SequenceOf where

open Base256
open Aeres.Grammar.Definitions UInt8

data SequenceOf (@0 A : List UInt8 → Set) : @0 List UInt8 → Set

record SequenceOfFields (@0 A : List Dig → Set) (@0 bs : List Dig) : Set where
  inductive
  constructor mkSequenceOf
  field
    @0 {bs₁ bs₂} : List Dig
    h : A bs₁
    t : SequenceOf A bs₂
    @0 bs≡ : bs ≡ bs₁ ++ bs₂

data SequenceOf A where
  nil : SequenceOf A []
  cons : ∀ {@0 xs} → SequenceOfFields A xs → SequenceOf A xs

lengthSequence : ∀ {@0 A xs} → SequenceOf A xs → ℕ
lengthSequence nil = 0
lengthSequence (cons (mkSequenceOf h t bs≡)) = 1 + lengthSequence t

BoundedSequenceOf : (@0 A : List Dig → Set) → @0 ℕ → @0 List Dig → Set
BoundedSequenceOf A n = Σₚ (SequenceOf A) λ _ seq → lengthSequence seq ≥ n

NonEmptySequenceOf : (@0 A : List Dig → Set) → @0 List Dig → Set
NonEmptySequenceOf A = BoundedSequenceOf A 1

Seq : (A : List Dig → Set) → (@0 _ : List Dig) → Set
Seq A = TLV Tag.Sequence (SequenceOf A)

NonEmptySeq : (@0 A : List Dig → Set) → @0 List Dig → Set
NonEmptySeq A = TLV Tag.Sequence (NonEmptySequenceOf A)


