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

record Base64Pad2 (@0 bs : List Char) : Set where
  constructor mk64P1
  field
    @0 {b₁ b₂} : Char
    c₁ : Base64Char [ b₁ ]
    c₂ : Base64Char [ b₂ ]
    @0 pad : toℕ (↑ Base64Char.i c₂) % (2 ^ 4) ≡ 0
    @0 bs≡ : bs ≡ b₁ ∷ b₂ ∷ '=' ∷ [ '=' ]

record Base64Pad1 (@0 bs : List Char) : Set where
  constructor mk64P1
  field
    @0 {b₁ b₂ b₃} : Char
    c₁ : Base64Char [ b₁ ]
    c₂ : Base64Char [ b₂ ]
    c₃ : Base64Char [ b₃ ]
    @0 pad : toℕ (↑ Base64Char.i c₃) % (2 ^ 2) ≡ 0
    @0 bs≡ : bs ≡ b₁ ∷ b₂ ∷ b₃ ∷ [ '=' ]

data Base64Pad (@0 bs : List Char) : Set where
  pad0 : bs ≡ []       → Base64Pad bs
  pad1 : Base64Pad1 bs → Base64Pad bs
  pad2 : Base64Pad2 bs → Base64Pad bs

record Base64Str (@0 bs : List Char) : Set where
  constructor mk64Str
  field
    @0 {s p} : List Char
    str : IList Base64Char s
    @0 strLen : length s % 4 ≡ 0
    pad : Base64Pad p
    @0 bs≡ : bs ≡ s ++ p
