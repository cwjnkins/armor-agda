{-# OPTIONS --subtyping #-}

open import Aeres.Binary
import      Aeres.Grammar.IList.TCB
open import Aeres.Prelude

module Aeres.Data.Unicode.UTF32.TCB where

open Aeres.Grammar.IList.TCB UInt8

-- • Because surrogate code points are not included in the set of Unicode scalar
--   values, UTF-32 code units in the range 0000D800..0000DFFF are ill-formed.
-- • Any UTF-32 code unit greater than 0010FFFF is ill-formed

data UTF32CharRange : (@0 b₂ b₃ b₄ : UInt8) → Set where
  00000000-0000d7ff : ∀ {@0 b₃ b₄} → toℕ b₃ ≤ 215 → UTF32CharRange (# 0) b₃ b₄
  0000e000-0000ffff : ∀ {@0 b₃ b₄} → toℕ b₃ ≥ 224 → UTF32CharRange (# 0) b₃ b₄
  00010000-0010ffff : ∀ {@0 b₂ b₃ b₄} → InRange 1 2 b₂ → UTF32CharRange b₂ b₃ b₄

record UTF32Char (@0 bs : List UInt8) : Set where
  constructor mkUTF32Char
  field
    b₂ b₃ b₄ : UInt8
    @0 range : UTF32CharRange b₂ b₃ b₄
    @0 bs≡ : bs ≡ (# 0) ∷ b₂ ∷ b₃ ∷ [ b₄ ]

UTF32 : @0 List UInt8 → Set
UTF32 = IList UTF32Char