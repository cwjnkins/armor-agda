{-# OPTIONS --subtyping #-}

open import Aeres.Prelude
open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X690-DER.Int
open import Data.Nat.Properties
  hiding (_≟_)

module Aeres.Data.X509.Properties.Primitives where

open Base256
open import Aeres.Grammar.Definitions Dig

module BoolValue where
  nonempty : NonEmpty Generic.BoolValue
  nonempty () refl

  @0 nonnesting : NonNesting Generic.BoolValue
  nonnesting x (Generic.mkBoolValue v b vᵣ bs≡) (Generic.mkBoolValue v₁ b₁ vᵣ₁ bs≡₁) =
    proj₁ $ Lemmas.length-++-≡ _ _ _ _ x (trans (cong length bs≡) (cong length (sym bs≡₁)))

  @0 unambiguous : Unambiguous Generic.BoolValue
  unambiguous (Generic.mkBoolValue .#0 .(# 0) Generic.falseᵣ refl) (Generic.mkBoolValue .#0 .(# 0) Generic.falseᵣ refl) = refl
  unambiguous (Generic.mkBoolValue .#0 .(# 0) Generic.falseᵣ refl) (Generic.mkBoolValue .#1 .(# 255) Generic.trueᵣ ())
  unambiguous (Generic.mkBoolValue .#1 .(# 255) Generic.trueᵣ refl) (Generic.mkBoolValue .#0 .(# 0) Generic.falseᵣ ())
  unambiguous (Generic.mkBoolValue .#1 .(# 255) Generic.trueᵣ refl) (Generic.mkBoolValue .#1 .(# 255) Generic.trueᵣ refl) = refl

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
