{-# OPTIONS --subtyping #-}

open import Aeres.Prelude
open import Data.Nat.Properties
  hiding (_≟_)

module Aeres.Grammar.Parser.Core (Σ : Set) where

record Success (A : List Σ → Set) (xs : List Σ) : Set where
  constructor success
  field
    @0 prefix : List Σ
    read   : ℕ
    @0 read≡ : read ≡ length prefix
    value  : A prefix
    suffix : List Σ
    @0 ps≡    : prefix ++ suffix ≡ xs

mapSuccess : ∀ {A B : List Σ → Set} → (∀ {@0 xs} → A xs → B xs) → ∀ {@0 xs} → Success A xs → Success B xs
mapSuccess f (success prefix read read≡ value suffix ps≡ ) = success prefix read read≡ (f value) suffix ps≡

record Parserᵢ (M : List Σ → Set → Set) (A : List Σ → Set) : Set where
  constructor mkParser
  field
    runParser : (xs : List Σ) → M xs (Success A xs)
open Parserᵢ public

Parser : (M : Set → Set) (A : List Σ → Set) → Set
Parser M = Parserᵢ (const M)
