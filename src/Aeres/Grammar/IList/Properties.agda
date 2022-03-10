{-# OPTIONS --subtyping #-}

open import Aeres.Prelude
  hiding (head ; tail)

module Aeres.Grammar.IList.Properties (Σ : Set) where

open import Aeres.Grammar.Definitions Σ
open import Aeres.Grammar.IList       Σ
open import Aeres.Grammar.Sum         Σ

module IListProps where
  Rep : (List Σ → Set) → @0 List Σ → Set
  Rep A = Sum (_≡ []) (&ₚ A (IList A))

  equiv : ∀ {@0 A} → Equivalent (Rep A) (IList A)
  proj₁ equiv (Sum.inj₁ refl) = nil
  proj₁ equiv (Sum.inj₂ (mk&ₚ fstₚ₁ sndₚ₁ bs≡)) =
    consIList fstₚ₁ sndₚ₁ bs≡
  proj₂ equiv nil = inj₁ refl
  proj₂ equiv (consIList h t bs≡) =
    inj₂ (mk&ₚ h t bs≡)

  iso : ∀ {@0 A} → Iso (Rep A) (IList A)
  proj₁ iso = equiv
  proj₁ (proj₂ iso) (Sum.inj₁ refl) = refl
  proj₁ (proj₂ iso) (Sum.inj₂ (mk&ₚ fstₚ₁ sndₚ₁ bs≡)) = refl
  proj₂ (proj₂ iso) nil = refl
  proj₂ (proj₂ iso) (consIList h t bs≡) = refl

  @0 unambiguous : ∀ {@0 A} → Unambiguous A → NonEmpty A → NonNesting A → Unambiguous (IList A)
  unambiguous ua ne nn nil nil = refl
  unambiguous ua ne nn{xs} nil (cons (mkIListCons{bs₁}{bs₂} h t bs≡)) =
    contradiction (++-conicalˡ _ _ (sym bs≡)) (ne h)
  unambiguous ua ne nn {xs} (cons (mkIListCons h t bs≡)) nil =
    contradiction (++-conicalˡ _ _ (sym bs≡)) (ne h)
  unambiguous{A} ua ne nn (consIList{bs₁₁}{bs₁₂} h t bs≡) (consIList{bs₂₁}{bs₂₂} h₁ t₁ bs≡₁) =
    ≡-elim (λ {bs₂₁} bs₁≡ → ∀ h₁ bs≡₁ → _ ≡ cons (mkIListCons{bs₁ = bs₂₁} h₁ t₁ bs≡₁))
      (λ h₁ bs≡₁ →
        ≡-elim (λ {bs₂₂} bs₂≡ → ∀ t₁ bs≡₁ → _ ≡ cons (mkIListCons h₁ t₁ bs≡₁))
          (λ t₁ bs≡₁ →
            subst₂ (λ x y → _ ≡ cons (mkIListCons x y bs≡₁)) (ua h h₁) (unambiguous ua ne nn t t₁)
              (subst₀ (λ x → _ ≡ cons (mkIListCons _ _ x)) (≡-unique bs≡ bs≡₁) refl))
          bs₂≡ t₁ bs≡₁)
      bs₁≡ h₁ bs≡₁
    where
    @0 bs≡' : bs₁₁ ++ bs₁₂ ≡ bs₂₁ ++ bs₂₂
    bs≡' = trans₀ (sym bs≡) bs≡₁

    @0 bs₁≡ : bs₁₁ ≡ bs₂₁
    bs₁≡ = nn bs≡' h h₁

    bs₂≡ : bs₁₂ ≡ bs₂₂
    bs₂≡ = Lemmas.++-cancel≡ˡ _ _ bs₁≡ bs≡'
