{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Prelude

open import Aeres.Grammar.IList Char
open import Aeres.Grammar.Sum   Char

module Aeres.Data.Base64.TCB where

record Base64Char (@0 bs : List Char) : Set where
  constructor mk64
  field
    @0 c : Char
    @0 c∈ : c ∈ Base64.charset
    i : Singleton (Any.index c∈)
    @0 bs≡ : bs ≡ [ c ]

data Pad : @0 List Char → Set where
  pad0 : Pad []
  pad1 : Pad (String.toList "=")
  pad2 : Pad (String.toList "==")

record Base64Str (@0 bs : List Char) : Set where
  constructor mk64Str
  field
    @0 s p : List Char
    str : IList Base64Char s
    pad : Pad p
    @0 mult : length (s ++ p) % 4 ≡ 0
    @0 bs≡ : bs ≡ s ++ p
