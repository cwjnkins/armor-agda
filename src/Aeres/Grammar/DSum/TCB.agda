{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

module Aeres.Grammar.DSum.TCB (Σ : Set) where


-- Discriminated sum with bounded look-ahead
record DSum {n : ℕ} (A : Vec Σ n → Set) (B : {xs : Vec Σ n} → A xs → List Σ → Set) (@0 xs : List Σ) : Set where
  constructor mkDSum
  field
    @0 {look} : Vec Σ n
    discr : A look
    value : B discr xs
    @0 look≡ : Vec.toList look ≡ take n xs
