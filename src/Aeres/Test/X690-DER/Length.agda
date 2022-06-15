{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER
open import Aeres.Grammar.Parser
open import Aeres.Prelude

module Aeres.Test.X690-DER.Length where

open Base256

len₁bs : List UInt8
len₁bs = # 130 ∷ # 13 ∷ [ # 82 ]

len₁ : Length len₁bs
len₁ = Length.longₛ (# 130) (# 13) [ # 82 ]

len₁p : Logging.val (runParser parseLen len₁bs) ≡ yes (success _ 3 refl (Length.longₛ (# 130) (# 13) [ # 82 ]) [] refl)
len₁p = refl

len₂bs : List UInt8
len₂bs = [ # 127 ]

len₂ : Length len₂bs
len₂ = Length.shortₛ (# 127)

len₂p : Logging.val (runParser parseLen len₂bs) ≡ yes (success _ 1 refl (Length.shortₛ (# 127)) [] refl)
len₂p = refl

len₃p : isNo (Logging.val (runParser parseLen [ # 128 ])) ≡ true
len₃p = refl
