{-# OPTIONS --subtyping #-}

open import Aeres.Prelude
open import Aeres.Binary
open import Aeres.Data.X509
  hiding (module BoolValue)
open import Aeres.Data.X690-DER.Int
open import Data.Nat.Properties
  hiding (_≟_)

module Aeres.Data.X509.Properties.Primitives where

open Base256
open import Aeres.Grammar.Definitions Dig

module IntegerValue where
  @0 unambiguous : Unambiguous IntegerValue
  unambiguous{xs} self self = refl

module BitstringValue where
  @0 unambiguous : Unambiguous BitStringValue
  unambiguous (mkBitStringValue bₕ bₜ bₕ<8 bits unusedBits bs≡) (mkBitStringValue bₕ₁ bₜ₁ bₕ<9 bits₁ unusedBits₁ bs≡₁) =
    subst₂
      (λ bₕ₁ bₜ₁ → ∀ (bₕ₁<8 : toℕ bₕ₁ < 8) (bits₁ : Singleton (BitString.toBitRep bₕ₁ bₜ₁)) (unusedBits₁ : BitString.UnusedBits bₕ₁ bₜ₁) bs≡₁ →
        _ ≡ mkBitStringValue bₕ₁ bₜ₁ bₕ₁<8 bits₁ unusedBits₁ bs≡₁)
      bₕ≡ bₜ≡
      (λ bₕ₁<8 bits₁ unusedBits₁ bs≡₁ →
        subst₂ (λ bₕ₁<8 bs≡₁ → _ ≡ mkBitStringValue bₕ bₜ bₕ₁<8 bits₁ unusedBits₁ bs≡₁ ) (≤-irrelevant bₕ<8 _) (≡-unique bs≡ _)
          (subst₂ (λ bits₁ unusedBits₁ → _ ≡ mkBitStringValue bₕ bₜ bₕ<8 bits₁ unusedBits₁ bs≡)
            (uniqueSingleton bits _) (‼ BitString.uniqueUnusedBits{bₕ}{bₜ} unusedBits unusedBits₁)
            refl))
      bₕ<9 bits₁ unusedBits₁ bs≡₁
    where
    @0 bₕ≡ : bₕ ≡ bₕ₁
    bₕ≡ = ∷-injectiveˡ (trans₀ (sym bs≡) bs≡₁)

    @0 bₜ≡ : bₜ ≡ bₜ₁
    bₜ≡ = ∷-injectiveʳ ((trans₀ (sym bs≡) bs≡₁))
