{-# OPTIONS --subtyping #-}

open import Aeres.Prelude
open import Aeres.Binary
open import Aeres.Data.X509
import      Aeres.Grammar.Definitions
open import Data.Nat.Properties
  hiding (_≟_)

module Aeres.Data.X509.Properties.BitstringValue where

open Base256
open Aeres.Grammar.Definitions Dig

@0 unambiguous : Unambiguous Generic.BitstringValue
unambiguous (Generic.mkBitstringValue bₕ₁ bₜ₁ bₕ₁<8 bits₁ unusedBits₁ bs≡₁) (Generic.mkBitstringValue bₕ₂ bₜ₂ bₕ₂<8 bits₂ unusedBits₂ bs≡₂) =
  ≡-elim (λ {bₕ₂} bₕ≡ → ∀ bₕ₂<8 bits₂ unusedBits₂ bs≡₂ → Generic.mkBitstringValue bₕ₁ bₜ₁ bₕ₁<8 bits₁ unusedBits₁ bs≡₁ ≡ Generic.mkBitstringValue bₕ₂ bₜ₂ bₕ₂<8 bits₂ unusedBits₂ bs≡₂)
    (λ bₕ₂<8 bits₂ unusedBits₂ bs≡₂' →
      ≡-elim (λ {bₜ₂} bₜ≡ → ∀ (bits₂ : Singleton (Generic.toBitRep bₕ₁ bₜ₂)) unusedBits₂ bs≡₂ → Generic.mkBitstringValue bₕ₁ bₜ₁ bₕ₁<8 bits₁ unusedBits₁ bs≡₁ ≡ Generic.mkBitstringValue bₕ₁ bₜ₂ bₕ₂<8 bits₂ unusedBits₂ bs≡₂)
        (λ bits₂ unusedBits₂ bs≡₂' →
          subst₂ (λ bits bs≡ → _ ≡ Generic.mkBitstringValue bₕ₁ bₜ₁ _ bits _ bs≡) (uniqueSingleton bits₁ bits₂) (≡-unique bs≡₁ bs≡₂')
            (subst₂ (λ x y → _ ≡ Generic.mkBitstringValue bₕ₁ bₜ₁ x _ y _) (≤-irrelevant bₕ₁<8 bₕ₂<8) (Generic.bitstringUnusedBits-unique{bₜ = bₜ₁} unusedBits₁ unusedBits₂)
              refl))
        bₜ≡ bits₂ unusedBits₂ bs≡₂')
    bₕ≡ bₕ₂<8 bits₂ unusedBits₂ bs≡₂
  where
  @0 bs≡ : bₕ₁ ∷ bₜ₁ ≡ bₕ₂ ∷ bₜ₂
  bs≡ = trans₀ (sym bs≡₁) bs≡₂

  @0 bₕ≡ : bₕ₁ ≡ bₕ₂
  bₕ≡ = ∷-injectiveˡ bs≡

  @0 bₜ≡ : _
  bₜ≡ = ∷-injectiveʳ bs≡
