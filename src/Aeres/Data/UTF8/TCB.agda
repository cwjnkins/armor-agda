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

UTF8Char : @0 List UInt8 → Set
UTF8Char =
  Sum  UTF8Char1
  (Sum UTF8Char2
  (Sum UTF8Char3
       UTF8Char4))

pattern uft81 b₁ b₁range bs≡ =
  Sum.inj₁ (mkUTF8Char1 b₁ b₁range bs≡)
pattern uft82 b₁ b₂ b₁range b₂range bs≡ =
  Sum.inj₂ (Sum.inj₁ (mkUTF8Char2 b₁ b₂ b₁range b₂range bs≡))
pattern uft83 b₁ b₂ b₃ b₁range b₂range b₃range bs≡ =
  Sum.inj₂ (Sum.inj₂ Sum.inj₁ (mkUTF8Char2 b₁ b₂ b₃ b₁range b₂range b₃range bs≡))
pattern uft84 b₁ b₂ b₃ b₄ b₁range b₂range b₃range b₄range bs≡ =
  Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ (mkUTF8Char2 b₁ b₂ b₃ b₄ b₁range b₂range b₃range b₄range bs≡))))

UTF8 : @0 List UInt8 → Set
UTF8 = IList UTF8Char
