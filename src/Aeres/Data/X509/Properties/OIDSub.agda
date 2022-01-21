{-# OPTIONS --subtyping #-}

open import Aeres.Prelude
open import Aeres.Binary
open import Aeres.Data.X509
import Aeres.Grammar.Definitions
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Properties.OIDSub where

open Base256
open Aeres.Grammar.Definitions Dig

nonempty : NonEmpty Generic.OIDSub
nonempty (Generic.mkOIDSub [] lₚ≥128 lₑ lₑ<128 leastDigs ()) refl
nonempty (Generic.mkOIDSub (x ∷ lₚ) lₚ≥128 lₑ lₑ<128 leastDigs ()) refl

@0 unambiguous : Unambiguous Generic.OIDSub
unambiguous (Generic.mkOIDSub lₚ lₚ≥128 lₑ lₑ<128 leastDigs refl) (Generic.mkOIDSub lₚ₁ lₚ≥129 lₑ₁ lₑ<129 leastDigs₁ bs≡₁) =
  ≡-elim (λ {lₚ₁} lₚ≡ → ∀ lₚ₁≥128 leastDigs₁ bs≡₁ → Generic.mkOIDSub lₚ lₚ≥128 lₑ lₑ<128 leastDigs refl ≡ Generic.mkOIDSub lₚ₁ lₚ₁≥128 lₑ₁ lₑ<129 leastDigs₁ bs≡₁)
    (λ lₚ₁≥128 leastDigs₁ bs≡₁' →
      ≡-elim (λ {lₑ₁} lₑ≡ → ∀ lₑ₁<128 bs≡₁ → Generic.mkOIDSub lₚ lₚ≥128 lₑ lₑ<128 leastDigs refl ≡ Generic.mkOIDSub lₚ lₚ₁≥128 lₑ₁ lₑ₁<128 leastDigs₁ bs≡₁)
        (λ where
          lₑ₁<128 refl → ‼
            subst₂ (λ x y → Generic.mkOIDSub lₚ lₚ≥128 lₑ lₑ<128 leastDigs refl ≡ Generic.mkOIDSub lₚ x lₑ y leastDigs₁ refl)
              (All.irrelevant ≤-irrelevant lₚ≥128 _) (≤-irrelevant lₑ<128 _)
              (subst₀ (λ x → Generic.mkOIDSub lₚ lₚ≥128 lₑ lₑ<128 leastDigs refl ≡ Generic.mkOIDSub _ lₚ≥128 _ lₑ<128 x refl) (Generic.oidLeastDigs-unique{bs = lₚ} leastDigs leastDigs₁)
                refl))
        lₑ≡ lₑ<129 bs≡₁')
    lₚ≡ lₚ≥129 leastDigs₁ bs≡₁
  where
  @0 lₚ≡ : lₚ ≡ lₚ₁
  lₚ≡ = ∷ʳ-injectiveˡ _ _ bs≡₁

  @0 lₑ≡ : lₑ ≡ lₑ₁
  lₑ≡ = ∷ʳ-injectiveʳ _ _ bs≡₁

instance
  OIDSub≋ : Eq≋ Generic.OIDSub
  Eq≋._≋?_ OIDSub≋ {bs} {bs₁} a₁@(Generic.mkOIDSub lₚ lₚ≥128 lₑ lₑ<128 leastDigs bs≡) a₂@(Generic.mkOIDSub lₚ₁ lₚ≥129 lₑ₁ lₑ<129 leastDigs₁ bs≡₁)
    with lₚ ∷ʳ lₑ ≟ lₚ₁ ∷ʳ lₑ₁
  ... | yes bs≡bs₁ =
    yes (mk≋ bs≡bs₁' (unambiguous (subst Generic.OIDSub bs≡bs₁' a₁) a₂))
    where
    @0 bs≡bs₁' : bs ≡ bs₁
    bs≡bs₁' = trans bs≡ (trans bs≡bs₁ (sym bs≡₁))
  ... | no ¬bs≡bs₁ = no λ where
    (mk≋ bs≡bs₁ a≡) → contradiction (trans (sym bs≡) (trans bs≡bs₁ bs≡₁)) ¬bs≡bs₁

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
