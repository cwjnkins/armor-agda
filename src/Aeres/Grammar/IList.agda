{-# OPTIONS --subtyping #-}

open import Aeres.Prelude
  hiding (head ; tail)

module Aeres.Grammar.IList (Σ : Set) where

open import Aeres.Grammar.Definitions Σ

data IList (@0 A : List Σ → Set) : @0 List Σ → Set

record IListCons (@0 A : List Σ → Set) (@0 bs : List Σ) : Set where
  inductive
  constructor mkIListCons
  field
    @0 {bs₁ bs₂} : List Σ
    head : A bs₁
    tail : IList A bs₂
    @0 bs≡ : bs ≡ bs₁ ++ bs₂

data IList A where
  nil : IList A []
  cons : ∀ {@0 xs} → IListCons A xs → IList A xs

lengthSequence : ∀ {@0 A xs} → IList A xs → ℕ
lengthSequence nil = 0
lengthSequence (cons (mkIListCons h t bs≡)) = 1 + lengthSequence t

pattern consIList bs₁ bs₂ h t bs≡ = cons (mkIListCons{bs₁}{bs₂} h t bs≡)
