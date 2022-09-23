{-# OPTIONS --subtyping #-}

import      Aeres.Grammar.IList.TCB
open import Aeres.Prelude
  hiding (head ; tail)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Grammar.IList.Properties (Σ : Set) where

open import Aeres.Grammar.Definitions Σ
open        Aeres.Grammar.IList.TCB   Σ
open import Aeres.Grammar.Sum         Σ

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

lengthIList≡
  : ∀ {@0 A} → NonEmpty A → NonNesting A
    → ∀ {@0 xs} → (il₁ il₂ : IList A xs)
    → lengthIList il₁ ≡ lengthIList il₂
lengthIList≡ ne nn nil nil = refl
lengthIList≡ ne nn nil (cons (mkIListCons head tail bs≡)) =
  contradiction
    (++-conicalˡ _ _ (sym bs≡))
    (ne head)
lengthIList≡ ne nn (cons (mkIListCons head tail bs≡)) nil =
  contradiction
    (++-conicalˡ _ _ (sym bs≡))
    (ne head)
lengthIList≡{A} ne nn (cons (mkIListCons{bs₂ = bs₂} head tail refl)) (cons (mkIListCons head₁ tail₁ bs≡₁)) =
  cong suc
    (trans (lengthIList≡ ne nn {bs₂} tail tail')
      (‼ ≡-elim (λ {bs₁'} eq → lengthIList (subst₀ (IList A) eq tail₁) ≡ lengthIList tail₁) refl bs₂≡))
  where
  @0 bs₁≡ : _ ≡ _
  bs₁≡ = nn (sym bs≡₁) head₁ head

  @0 bs₂≡ : _ ≡ _
  bs₂≡ = Lemmas.++-cancel≡ˡ _ _ bs₁≡ (sym bs≡₁)

  tail' : IList A bs₂
  tail' = subst₀ (IList A) bs₂≡ tail₁

lengthIList≤
  : ∀ {@0 A} → NonEmpty A → NonNesting A
    → (@0 xs₁ xs₂ : List Σ) {@0 ys₁ ys₂ : List Σ}
    → xs₁ ++ ys₁ ≡ xs₂ ++ ys₂
    → @0 length xs₁ ≤ length xs₂
    → (v₁ : IList A xs₁) (v₂ : IList A xs₂)
    → lengthIList v₁ ≤ lengthIList v₂
lengthIList≤ ne nn .[] xs₂ ++≡ xs₁≤ nil v₂ = z≤n
lengthIList≤ ne nn .(bs₁ ++ bs₂) .[] ++≡ xs₁≤ (consIList{bs₁}{bs₂} head₁ tail₁ refl) nil =
  contradiction bs₁≡ (ne head₁)
  where
  @0 bs₁≡ : bs₁ ≡ []
  bs₁≡ = case (singleton bs₁ refl) of λ where
    (singleton [] refl) → refl
    (singleton (x ∷ x₁) refl) →
      contradiction xs₁≤ λ where ()
lengthIList≤ ne nn .(bs₁ ++ bs₂) xs₂{ys₁ = ys₁}{ys₂} ++≡ xs₁≤ (consIList{bs₁}{bs₂} head₁ tail₁ refl) (consIList{bs₁'}{bs₂'} head₂ tail₂ refl) =
  ≤.begin (1 + lengthIList tail₁
            ≤.≤⟨ +-monoʳ-≤ 1 (lengthIList≤ ne nn bs₂ bs₂'
                   (‼ Lemmas.++-cancel≡ˡ _ _ bs₁≡ ++≡')
                   bs₂≤ tail₁ tail₂) ⟩
          1 + lengthIList tail₂ ≤.∎)
  where
  open import Data.Nat.Properties
  open ≡-Reasoning
  module ≤ = ≤-Reasoning

  @0 ++≡' : bs₁ ++ bs₂ ++ ys₁ ≡ bs₁' ++ bs₂' ++ ys₂
  ++≡' =
    (begin bs₁ ++ bs₂ ++ ys₁ ≡⟨ solve (++-monoid Σ) ⟩
           (bs₁ ++ bs₂) ++ ys₁ ≡⟨ ++≡ ⟩
           (bs₁' ++ bs₂') ++ ys₂ ≡⟨ solve (++-monoid Σ) ⟩
           bs₁' ++ bs₂' ++ ys₂ ∎)

  @0 bs₁≡ : bs₁ ≡ bs₁'
  bs₁≡ = nn ++≡' head₁ head₂

  @0 bs₂≤ : length bs₂ ≤ length bs₂'
  bs₂≤ = +-cancelˡ-≤ (length bs₁)
           (≤.begin (length bs₁ + length bs₂ ≤.≡⟨ sym (length-++ bs₁) ⟩
                    length (bs₁ ++ bs₂) ≤.≤⟨ xs₁≤ ⟩
                    length (bs₁' ++ bs₂') ≤.≡⟨ length-++ bs₁' ⟩
                    length bs₁' + length bs₂' ≤.≡⟨ cong ((_+ _) ∘ length) (sym bs₁≡) ⟩
                    length bs₁ + length bs₂' ≤.∎))
