{-# OPTIONS --subtyping #-}

open import Aeres.Prelude
open import Data.Nat.Properties
  hiding (_≟_)

module Aeres.Grammar.Parser.WellFounded (Σ : Set) where

open import Aeres.Grammar.Parser.Core Σ

ParserWF : (M : Set → Set) (A : List Σ → Set) → Set
ParserWF M A = Parserᵢ (λ xs X → (@0 _ : Acc _<_ (length xs)) → M X) A

parseWF : {M : Set → Set} {A : List Σ → Set} → ParserWF M A → Parser M A
runParser (parseWF p) xs = runParser p xs (<-wellFounded (length xs))
  where open import Data.Nat.Induction
