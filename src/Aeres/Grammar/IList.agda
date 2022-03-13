{-# OPTIONS --subtyping #-}

open import Aeres.Prelude
  hiding (head ; tail)
open import Tactic.MonoidSolver using (solve ; solve-macro)

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

appendIList : ∀ {@0 A xs₁ xs₂} → IList A xs₁ → IList A xs₂ → IList A (xs₁ ++ xs₂)
appendIList nil x₁ = x₁
appendIList (cons (mkIListCons head tail refl)) x₁
  with appendIList tail x₁
... | y = cons (mkIListCons head y  (solve (++-monoid Σ)))

reverseIList : ∀ {@0 A xs} → IList A xs → Exists─ _ (IList A)
reverseIList x = helper x nil
  where
  helper : ∀ {@0 A xs₁ xs₂} → IList A xs₁ → IList A xs₂ → Exists─ _ (IList A)
  helper nil x₁ = _ , x₁
  helper (cons (mkIListCons head tail bs≡)) x₁ = helper tail (appendIList (cons (mkIListCons head nil refl)) x₁)

lengthIList : ∀ {@0 A xs} → IList A xs → ℕ
lengthIList nil = 0
lengthIList (cons (mkIListCons h t bs≡)) = 1 + lengthIList t

IListLowerBounded : (@0 A : List Σ → Set) → @0 ℕ → @0 List Σ → Set
IListLowerBounded A n = Σₚ (IList A) (λ s xs → lengthIList xs ≥ n)

IListNonEmpty : (@0 A : List Σ → Set) → @0 List Σ → Set
IListNonEmpty A = IListLowerBounded A 1

pattern consIList{bs₁}{bs₂} h t bs≡ = cons (mkIListCons{bs₁}{bs₂} h t bs≡)
