{-# OPTIONS --subtyping #-}

open import Aeres.Prelude
open import Aeres.Binary
open import Aeres.Data.X509
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Properties.OIDSub where

open Base256
open import Aeres.Grammar.Definitions Dig

nonempty : NonEmpty Generic.OIDSub
nonempty (Generic.mkOIDSub [] lₚ≥128 lₑ lₑ<128 leastDigs ()) refl
nonempty (Generic.mkOIDSub (x ∷ lₚ) lₚ≥128 lₑ lₑ<128 leastDigs ()) refl

@0 nonnesting : NonNesting Generic.OIDSub
nonnesting {ys₁ = ys₁} {ys₂ = ys₂} ++≡ (Generic.mkOIDSub lₚ₁ lₚ₁≥128 lₑ₁ lₑ₁<128 leastDigs₁ refl) (Generic.mkOIDSub lₚ₂ lₚ₂≥128 lₑ₂ lₑ₂<128 leastDigs₂ refl)
  with Lemmas.++-≡-⊆ (lₚ₁ ∷ʳ lₑ₁) _ (lₚ₂ ∷ʳ lₑ₂) _ ++≡
... | 0 , inj₁ xs₁⊆xs₂ = trans₀ (lₚ₁ ++ lₑ₁ ∷ [] ≡ (lₚ₁ ++ lₑ₁ ∷ []) ++ [] ∋ solve (++-monoid Dig)) xs₁⊆xs₂
... | 0 , inj₂ xs₂⊆xs₁ = trans₀ xs₂⊆xs₁ ((lₚ₂ ++ lₑ₂ ∷ []) ++ [] ≡ lₚ₂ ++ lₑ₂ ∷ [] ∋ solve (++-monoid Dig))
... | suc n , inj₁ xs₁⊆xs₂
  with ys₁
... | [] = trans₀ (lₚ₁ ++ lₑ₁ ∷ [] ≡ (lₚ₁ ++ lₑ₁ ∷ []) ++ [] ∋ solve (++-monoid Dig)) xs₁⊆xs₂
... | y₁ ∷ ys₁ =
  contradiction
    (lem xs₁⊆xs₂ lₚ₂≥128)
    (<⇒≱ lₑ₁<128)
  where
  -- TODO: refactor this.
  -- This is a general result about anything which is the result of a terminated "TakeWhile"
  lem : ∀ {ws w x xs ys y} → ws ∷ʳ w ++ x ∷ xs ≡ ys ∷ʳ y → All ((128 ≤_) ∘ toℕ) ys → 128 ≤ toℕ w
  lem {[]} {xs = xs} {y' ∷ ys} ++≡ (py' All.∷ ys≤128) rewrite ∷-injectiveˡ ++≡ = py'
  lem {x ∷ ws}{w} {xs = xs} {[]} ++≡ ys≤128 =
    contradiction
      (++-conicalˡ _ _ (∷-injectiveʳ ++≡))
      (Lemmas.∷ʳ⇒≢[]{xs = ws}{w})
  lem {x ∷ ws} {xs = xs} {x₁ ∷ ys} ++≡ (_ All.∷ ys≤128) = lem (∷-injectiveʳ ++≡) ys≤128
nonnesting {ys₁ = ys₁} {ys₂ = ys₂} ++≡ (Generic.mkOIDSub lₚ₁ lₚ₁≥128 lₑ₁ lₑ₁<128 leastDigs₁ refl) (Generic.mkOIDSub lₚ₂ lₚ₂≥128 lₑ₂ lₑ₂<128 leastDigs₂ refl) | suc n , inj₂ xs₂⊆xs₁
  with ys₂
... | [] = trans₀ xs₂⊆xs₁ ((lₚ₂ ++ lₑ₂ ∷ []) ++ [] ≡ lₚ₂ ++ lₑ₂ ∷ [] ∋ solve (++-monoid Dig))
... | y₂ ∷ ys₂ =
  contradiction
    (lem (sym xs₂⊆xs₁) lₚ₁≥128)
    (<⇒≱ lₑ₂<128)
  where
  lem : ∀ {ws w x xs ys y} → ws ∷ʳ w ++ x ∷ xs ≡ ys ∷ʳ y → All ((128 ≤_) ∘ toℕ) ys → 128 ≤ toℕ w
  lem {[]} {xs = xs} {y' ∷ ys} ++≡ (py' All.∷ ys≤128) rewrite ∷-injectiveˡ ++≡ = py'
  lem {x ∷ ws}{w} {xs = xs} {[]} ++≡ ys≤128 =
    contradiction
      (++-conicalˡ _ _ (∷-injectiveʳ ++≡))
      (Lemmas.∷ʳ⇒≢[]{xs = ws}{w})
  lem {x ∷ ws} {xs = xs} {x₁ ∷ ys} ++≡ (_ All.∷ ys≤128) = lem (∷-injectiveʳ ++≡) ys≤128
