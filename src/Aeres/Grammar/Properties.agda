{-# OPTIONS --subtyping #-}

open import Aeres.Prelude
open import Data.Nat.Properties
  hiding (_≟_)

module Aeres.Grammar.Properties (Σ : Set) where

open import Aeres.Grammar.Definitions Σ
open import Aeres.Grammar.Sum Σ

module Distribute where

  open ≡-Reasoning

  module _ {@0 A B : @0 List Σ → Set} where

    exactLength-& : ∀ {n} → Equivalent (ExactLength (&ₚ A B) n)
                          (&ₚᵈ (WithinLength A n)
                               (λ bs₁ _ → ExactLength B (n - length bs₁)))
    proj₁ (exactLength-&{n}) (mk×ₚ (mk&ₚ{bs₁ = bs₁}{bs₂} fstₚ₁ sndₚ₂ refl) (─ sndₚ₁) refl) =
      mk&ₚ (mk×ₚ fstₚ₁ (─ subst (length bs₁ ≤_) sndₚ₁ (Lemmas.length-++-≤₁ bs₁ _)) refl)
        (mk×ₚ sndₚ₂ (─ (begin length bs₂ ≡⟨ sym (m+n∸m≡n (length bs₁) _) ⟩
                            length bs₁ + length bs₂ - length bs₁ ≡⟨ cong (_- length bs₁) (sym (length-++ bs₁)) ⟩
                            length (bs₁ ++ bs₂) - length bs₁ ≡⟨ cong (_- length bs₁) sndₚ₁ ⟩
                            n - length bs₁ ∎)) refl)
        refl
    proj₂ (exactLength-&{n}) (mk&ₚ (mk×ₚ{bs = bs₁} fstₚ₁ (─ sndₚ₁) refl) (mk×ₚ{bs = bs₂} fstₚ₂ sndₚ₂ refl) refl) =
      mk×ₚ (mk&ₚ fstₚ₁ fstₚ₂ refl)
        (─ (begin length (bs₁ ++ bs₂) ≡⟨ length-++ bs₁ ⟩
                  length bs₁ + length bs₂ ≡⟨ cong (length bs₁ +_) (̂‼ sndₚ₂) ⟩
                  length bs₁ + (n - length bs₁) ≡⟨ m+[n∸m]≡n sndₚ₁ ⟩
                  n ∎))
        refl

    exactLength-Sum : ∀ {n} → Equivalent (ExactLength (Sum A B) n)
                                         (Sum (ExactLength A n) (ExactLength B n))
    proj₁ exactLength-Sum (mk×ₚ (inj₁ x) sndₚ₁ refl) = Sum.inj₁ (mk×ₚ x sndₚ₁ refl)
    proj₁ exactLength-Sum (mk×ₚ (inj₂ x) sndₚ₁ refl) = Sum.inj₂ (mk×ₚ x sndₚ₁ refl)
    proj₂ exactLength-Sum (inj₁ (mk×ₚ fstₚ₁ sndₚ₁ refl)) = mk×ₚ (Sum.inj₁ fstₚ₁) sndₚ₁ refl
    proj₂ exactLength-Sum (inj₂ (mk×ₚ fstₚ₁ sndₚ₁ refl)) = mk×ₚ (Sum.inj₂ fstₚ₁) sndₚ₁ refl

module NonNesting where

  open ≡-Reasoning
  open import Tactic.MonoidSolver using (solve ; solve-macro)

  noconfusion-option&₁ : ∀ {@0 A B} → NonNesting A → NonNesting B → NoConfusion A B → NonNesting (&ₚ (Option A) B)
  noconfusion-option&₁ nn₁ nn₂ nc ++≡ (mk&ₚ  none sndₚ₁ refl)    (mk&ₚ  none sndₚ₂ refl) = nn₂ ++≡ sndₚ₁ sndₚ₂
  noconfusion-option&₁ nn₁ nn₂ nc {xs₁ = xs₁}{ys₁}{xs₂}{ys₂} ++≡ (mk&ₚ  none sndₚ₁ refl)    (mk&ₚ{bs₁ = bs₁}{bs₂} (some x) sndₚ₂ bs≡₁) =
    ⊥-elim (nc ++≡' x sndₚ₁)
    where
    @0 ++≡' : bs₁ ++ bs₂ ++ ys₂ ≡ xs₁ ++ ys₁
    ++≡' = begin bs₁ ++ bs₂ ++ ys₂ ≡⟨ solve (++-monoid Σ) ⟩
                 (bs₁ ++ bs₂) ++ ys₂ ≡⟨ cong (_++ ys₂) (sym bs≡₁) ⟩
                 xs₂ ++ ys₂ ≡⟨ sym ++≡ ⟩
                 xs₁ ++ ys₁ ∎
  noconfusion-option&₁ nn₁ nn₂ nc {xs₁}{ys₁}{xs₂}{ys₂} ++≡ (mk&ₚ{bs₁ = bs₁}{bs₂} (some x) sndₚ₁ bs≡) (mk&ₚ  none sndₚ₂ refl) =
    ⊥-elim (nc ++≡' x sndₚ₂)
    where
    @0 ++≡' : bs₁ ++ bs₂ ++ ys₁ ≡ xs₂ ++ ys₂
    ++≡' = begin bs₁ ++ bs₂ ++ ys₁ ≡⟨ solve (++-monoid Σ) ⟩
                 (bs₁ ++ bs₂) ++ ys₁ ≡⟨ cong (_++ ys₁) (sym bs≡) ⟩
                 xs₁ ++ ys₁ ≡⟨ ++≡ ⟩
                 xs₂ ++ ys₂ ∎
  noconfusion-option&₁ nn₁ nn₂ nc ++≡ (mk&ₚ (some x) sndₚ₁ bs≡) (mk&ₚ (some x₁) sndₚ₂ bs≡₁) =
    ‼ (NonNesting&ₚ nn₁ nn₂ ++≡ (mk&ₚ x sndₚ₁ bs≡) (mk&ₚ x₁ sndₚ₂ bs≡₁))

module Unambiguous where

  open ≡-Reasoning
  open import Tactic.MonoidSolver using (solve ; solve-macro)

  unambiguous-option₁&₁ : ∀ {@0 A B} → Unambiguous A → NonNesting A → Unambiguous B → NonNesting B → NoConfusion A B → Unambiguous (&ₚ (Option A) B)
  unambiguous-option₁&₁ ua₁ nn₁ ua₂ nn₂ nc (mk&ₚ  none    sndₚ₁ refl) (mk&ₚ  none sndₚ₂ refl) = subst₀ (λ x → mk&ₚ none sndₚ₁ refl ≡ mk&ₚ none x refl) (ua₂ sndₚ₁ sndₚ₂) refl
  unambiguous-option₁&₁ ua₁ nn₁ ua₂ nn₂ nc {xs} (mk&ₚ  none    sndₚ₁ refl) (mk&ₚ{bs₁ = bs₁}{bs₂} (some x) sndₚ₂ bs≡₁) =
    ⊥-elim (nc bs≡'  x sndₚ₁)
    where
    @0 bs≡' : bs₁ ++ bs₂ ++ [] ≡ xs ++ []
    bs≡' = begin (bs₁ ++ bs₂ ++ [] ≡⟨ solve (++-monoid Σ) ⟩
                 bs₁ ++ bs₂ ≡⟨ sym bs≡₁ ⟩
                 xs ≡⟨ solve (++-monoid Σ) ⟩
                 xs ++ [] ∎)
  unambiguous-option₁&₁ ua₁ nn₁ ua₂ nn₂ nc {xs} (mk&ₚ{bs₁ = bs₁}{bs₂} (some x) sndₚ₁ bs≡) (mk&ₚ  none sndₚ₂ refl) =
    ⊥-elim (nc bs≡' x sndₚ₂)
    where
    @0 bs≡' : bs₁ ++ bs₂ ++ [] ≡ xs ++ []
    bs≡' = begin (bs₁ ++ bs₂ ++ [] ≡⟨ solve (++-monoid Σ) ⟩
                 bs₁ ++ bs₂ ≡⟨ sym bs≡ ⟩
                 xs ≡⟨ solve (++-monoid Σ) ⟩
                 xs ++ [] ∎)
  unambiguous-option₁&₁ ua₁ nn₁ ua₂ nn₂ nc (mk&ₚ (some x) sndₚ₁ bs≡) (mk&ₚ (some x₁) sndₚ₂ bs≡₁) =
    cong (λ where (mk&ₚ v₀ v₁ eq) → mk&ₚ (some v₀) v₁ eq ) (‼ pf)
    where
    @0 pf : mk&ₚ x sndₚ₁ bs≡ ≡ mk&ₚ x₁ sndₚ₂ bs≡₁
    pf = unambiguous&ₚ ua₁ nn₁ ua₂ nn₂ (mk&ₚ x sndₚ₁ bs≡) (mk&ₚ x₁ sndₚ₂ bs≡₁)

  unambiguous-&₁option₁ : ∀ {@0 A B} → Unambiguous A → NonNesting A → Unambiguous B → NonNesting B → NonEmpty B → Unambiguous (&ₚ A (Option B))
  unambiguous-&₁option₁{A}{B} ua₁ nn₁ ua₂ nn₂ nc (mk&ₚ{bs₁ = bs₁} fstₚ₁  none bs≡)    (mk&ₚ{bs₁ = bs₂} fstₚ₂  none bs≡₁) = ‼
    subst₀ (λ x → ∀ (fstₚ₂ : A x) bs≡₁ → mk&ₚ{A = A} fstₚ₁ none bs≡ ≡ mk&ₚ fstₚ₂ none bs≡₁)
      bs≡'
      (λ fstₚ₂ bs≡₁ →
        subst₂ (λ fstₚ₂ bs≡₁ → _ ≡ mk&ₚ fstₚ₂ none bs≡₁) (ua₁ fstₚ₁ fstₚ₂) (≡-unique bs≡ bs≡₁) refl)
      fstₚ₂ bs≡₁
    where
    @0 bs≡' : bs₁ ≡ bs₂
    bs≡' = ++-cancelʳ _ _ (trans₀ (sym bs≡) bs≡₁)
  unambiguous-&₁option₁ ua₁ nn₁ ua₂ nn₂ nc (mk&ₚ{bs₁ = bs₁} fstₚ₁  none bs≡)    (mk&ₚ{bs₁ = bs₂}{bs₃} fstₚ₂ (some x) bs≡₁) =
    ⊥-elim (contradiction (Lemmas.++-cancel≡ˡ _ _ (nn₁ (sym bs≡') fstₚ₂ fstₚ₁) (sym bs≡')) (nc x))
    where
    @0 bs≡' : bs₁ ++ [] ≡ bs₂ ++ bs₃
    bs≡' = trans₀ (sym bs≡) bs≡₁
  unambiguous-&₁option₁ ua₁ nn₁ ua₂ nn₂ nc (mk&ₚ{bs₁ = bs₂}{bs₃} fstₚ₁ (some x) bs≡) (mk&ₚ{bs₁ = bs₁} fstₚ₂  none bs≡₁) =
    ⊥-elim (contradiction (Lemmas.++-cancel≡ˡ _ _ (nn₁ (sym bs≡') fstₚ₁ fstₚ₂) (sym bs≡')) (nc x))
    where
    @0 bs≡' : bs₁ ++ [] ≡ bs₂ ++ bs₃
    bs≡' = trans₀ (sym bs≡₁) bs≡
  unambiguous-&₁option₁ ua₁ nn₁ ua₂ nn₂ nc (mk&ₚ fstₚ₁ (some x) bs≡) (mk&ₚ fstₚ₂ (some x₁) bs≡₁) =
    cong (λ where (mk&ₚ x y bs≡) → mk&ₚ x (some y) bs≡) (unambiguous&ₚ ua₁ nn₁ ua₂ nn₂ (mk&ₚ fstₚ₁ x bs≡) (mk&ₚ fstₚ₂ x₁ bs≡₁))
