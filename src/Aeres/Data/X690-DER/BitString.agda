{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

module Aeres.Data.X690-DER.BitString where

module BitString where
  open import Aeres.Data.X690-DER.TCB.BitString public

  uniqueUnusedBits : ∀ {bₕ bₜ} → Unique (UnusedBits bₕ bₜ)
  uniqueUnusedBits {bₜ = []} x y = ≡-unique x y
  uniqueUnusedBits {bₜ = x₁ ∷ []} x y = ≡-unique x y
  uniqueUnusedBits {bₜ = x₁ ∷ x₂ ∷ bₜ} x y = uniqueUnusedBits{bₜ = x₂ ∷ bₜ} x y

  unusedBits? : ∀ b bs → Dec (UnusedBits b bs)
  unusedBits? b [] = toℕ b ≟ 0
  unusedBits? b (x ∷ []) = toℕ x %2^ (toℕ b) ≟ 0
  unusedBits? b (x ∷ x₁ ∷ bs) = unusedBits? b (x₁ ∷ bs)

open BitString public
  hiding (UnusedBits ; toBitRep)

