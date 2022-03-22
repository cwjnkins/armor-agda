{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Prelude
import      Aeres.Grammar.IList
import      Aeres.Grammar.Sum

module Aeres.Data.UTF8.TCB where

open Base256
open Aeres.Grammar.IList UInt8
open Aeres.Grammar.Sum   UInt8

record UTF8Char1 (@0 bs : List UInt8) : Set where
  constructor mkUTF8Char1
  field
    b₁ : UInt8
    @0 b₁range : toℕ b₁ < 128
    @0 bs≡ : bs ≡ [ b₁ ]

record UTF8Char2 (@0 bs : List UInt8) : Set where
  constructor mkUTF8Char2
  field
    b₁ b₂ : UInt8
    @0 b₁range : InRange 192 223 b₁
    @0 b₂range : InRange 128 191 b₂
    @0 bs≡ : bs ≡ b₁ ∷ [ b₂ ]

record UTF8Char3 (@0 bs : List UInt8) : Set where
  constructor mkUTF8Char3
  field
    b₁ b₂ b₃ : UInt8
    @0 b₁range : InRange 224 239 b₁
    @0 b₂range : InRange 128 191 b₂
    @0 b₃range : InRange 128 191 b₃
    @0 bs≡ : bs ≡ b₁ ∷ b₂ ∷ [ b₃ ]

record UTF8Char4 (@0 bs : List UInt8) : Set where
  constructor mkUTF8Char4
  field
    b₁ b₂ b₃ b₄ : UInt8
    @0 b₁range : InRange 240 247 b₁
    @0 b₂range : InRange 128 191 b₂
    @0 b₃range : InRange 128 191 b₃
    @0 b₄range : InRange 128 191 b₄
    @0 bs≡ : bs ≡ b₁ ∷ b₂ ∷ b₃ ∷ [ b₄ ]

data UTF8Char (@0 bs : List UInt8) : Set where
  utf81 : UTF8Char1 bs → UTF8Char bs
  utf82 : UTF8Char2 bs → UTF8Char bs
  utf83 : UTF8Char3 bs → UTF8Char bs
  utf84 : UTF8Char4 bs → UTF8Char bs

UTF8 : @0 List UInt8 → Set
UTF8 = IList UTF8Char

instance
  -- TODO: come back to this if there are performance issues
  NumericUTF8Char : ∀ {@0 bs} → Numeric (UTF8Char bs)
  Numeric.toℕ NumericUTF8Char (utf81 x) =
     toℕ (UTF8Char1.b₁ x)
  Numeric.toℕ NumericUTF8Char (utf82 x) =
     toℕ (UTF8Char2.b₁ x) * (2 ^ 8) + toℕ (UTF8Char2.b₂ x)
  Numeric.toℕ NumericUTF8Char (utf83 x) =
     (toℕ $ UTF8Char3.b₁ x) * (2 ^ (8 * 2)) + (toℕ $ UTF8Char3.b₂ x) * (2 ^ 8) + toℕ (UTF8Char3.b₃ x)
  Numeric.toℕ NumericUTF8Char (utf84 x) =
      (toℕ $ UTF8Char4.b₁ x) * (2 ^ (8 * 3)) + (toℕ $ UTF8Char4.b₂ x) * 2 ^ (8 * 2)
    + (toℕ $ UTF8Char4.b₃ x) * 2 ^ 8 + (toℕ $ UTF8Char4.b₄ x)
