{-# OPTIONS --subtyping #-}

open import Aeres.Prelude
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
import      Aeres.Grammar.Sum
open import Data.Nat.Properties
  hiding (_≟_)
open import Data.List.Properties

module Aeres.Grammar.Properties (Σ : Set) where

open Aeres.Grammar.Definitions Σ
open Aeres.Grammar.Option      Σ
open Aeres.Grammar.Sum         Σ

module Distribute where

  open ≡-Reasoning

  module _ {@0 A B : @0 List Σ → Set} where

    ×ₚ-Σₚ-iso
      : ∀ {@0 C : (xs : List Σ) (a : A xs) → Set}
        → Iso ((Σₚ A C) ×ₚ B)
              (Σₚ (A ×ₚ B) λ _ x → C _ (fstₚ x))
    proj₁ (proj₁ ×ₚ-Σₚ-iso) (mk×ₚ (mk×ₚ a c refl) b refl) =
      mk×ₚ (mk×ₚ a b refl) c refl
    proj₂ (proj₁ ×ₚ-Σₚ-iso) (mk×ₚ (mk×ₚ a b refl) c refl) =
      mk×ₚ (mk×ₚ a c refl) b refl
    proj₁ (proj₂ ×ₚ-Σₚ-iso) (mk×ₚ (mk×ₚ a c refl) b refl) = refl
    proj₂ (proj₂ ×ₚ-Σₚ-iso) (mk×ₚ (mk×ₚ a b refl) c refl) = refl

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

  erased : ∀ {@0 A} → NonNesting A → NonNesting (Erased ∘ A)
  erased nn xs₁++ys₁≡ (─ a₁) (─ a₂) = ‼ (nn xs₁++ys₁≡ a₁ a₂)

  Restriction : (A B : List Σ → Set) → Set
  Restriction A B = ∀ {xs₁ ys₁ xs₂ ys₂} → xs₁ ++ ys₁ ≡ xs₂ ++ ys₂ → A xs₁ → B xs₂ → xs₁ ≡ xs₂

  @0 sumRestriction : ∀ {@0 A B} → NonNesting A → NonNesting B → Restriction A B → NonNesting (Sum A B)
  sumRestriction nn₁ nn₂ r xs₁++ys₁≡xs₂++ys₂ (Sum.inj₁ x) (Sum.inj₁ x₁) =
    nn₁ xs₁++ys₁≡xs₂++ys₂ x x₁
  sumRestriction nn₁ nn₂ r xs₁++ys₁≡xs₂++ys₂ (Sum.inj₁ x) (Sum.inj₂ x₁) =
    r xs₁++ys₁≡xs₂++ys₂ x x₁
  sumRestriction nn₁ nn₂ r xs₁++ys₁≡xs₂++ys₂ (Sum.inj₂ x) (Sum.inj₁ x₁) =
    sym (r (sym xs₁++ys₁≡xs₂++ys₂) x₁ x)
  sumRestriction nn₁ nn₂ r xs₁++ys₁≡xs₂++ys₂ (Sum.inj₂ x) (Sum.inj₂ x₁) =
    nn₂ xs₁++ys₁≡xs₂++ys₂ x x₁

module NoConfusion where
  equivalent : ∀ {@0 A₁ A₂ B} → Equivalent A₁ A₂ → NoConfusion A₁ B → NoConfusion A₂ B
  equivalent eqv nc {xs₁}{ys₁}{xs₂}{ys₂}++≡ a b = ‼ nc {xs₁}{xs₂ = xs₂}++≡ (proj₂ eqv a) b

  sumₚ : ∀ {@0 A B C} → NoConfusion A B → NoConfusion A C → NoConfusion A (Sum B C)
  sumₚ nc₁ nc₂ ++≡ a (Sum.inj₁ x) = nc₁ ++≡ a x
  sumₚ nc₁ nc₂ ++≡ a (Sum.inj₂ x) = nc₂ ++≡ a x

  sigmaₚ₁ : ∀ {@0 A₁ B₁ A₂ B₂} → NoConfusion A₁ A₂ → NoConfusion (Σₚ A₁ B₁) (Σₚ A₂ B₂)
  sigmaₚ₁ nc ++≡ (mk×ₚ fstₚ₁ sndₚ₁ refl) (mk×ₚ fstₚ₂ sndₚ₂ refl) = nc ++≡ fstₚ₁ fstₚ₂

  sigmaₚ₁ᵣ : ∀ {@0 A₁ A₂ B₂} → NoConfusion A₁ A₂ → NoConfusion A₁ (Σₚ A₂ B₂)
  sigmaₚ₁ᵣ nc ++≡ v₁ (mk×ₚ fstₚ₂ sndₚ₂ refl) = nc ++≡ v₁ fstₚ₂

module Unambiguous where

  open ≡-Reasoning
  open import Tactic.MonoidSolver using (solve ; solve-macro)

  option₁ : ∀ {@0 A} → Unambiguous A → NonEmpty A → Unambiguous (Option A)
  option₁ ua ne none none = refl
  option₁ ua ne none (some x) = contradiction refl (ne x)
  option₁ ua ne (some x) none = contradiction refl (ne x)
  option₁ ua ne (some x) (some x₁) = ‼ cong some (ua x x₁)

  unambiguous-option₁&₁ : ∀ {@0 A B} → Unambiguous A → NonNesting A → Unambiguous B → NoConfusion A B → Unambiguous (&ₚ (Option A) B)
  unambiguous-option₁&₁ ua₁ nn₁ ua₂ nc (mk&ₚ  none    sndₚ₁ refl) (mk&ₚ  none sndₚ₂ refl) = subst₀ (λ x → mk&ₚ none sndₚ₁ refl ≡ mk&ₚ none x refl) (ua₂ sndₚ₁ sndₚ₂) refl
  unambiguous-option₁&₁ ua₁ nn₁ ua₂ nc {xs} (mk&ₚ  none    sndₚ₁ refl) (mk&ₚ{bs₁ = bs₁}{bs₂} (some x) sndₚ₂ bs≡₁) =
    ⊥-elim (nc bs≡'  x sndₚ₁)
    where
    @0 bs≡' : bs₁ ++ bs₂ ++ [] ≡ xs ++ []
    bs≡' = begin (bs₁ ++ bs₂ ++ [] ≡⟨ solve (++-monoid Σ) ⟩
                 bs₁ ++ bs₂ ≡⟨ sym bs≡₁ ⟩
                 xs ≡⟨ solve (++-monoid Σ) ⟩
                 xs ++ [] ∎)
  unambiguous-option₁&₁ ua₁ nn₁ ua₂ nc {xs} (mk&ₚ{bs₁ = bs₁}{bs₂} (some x) sndₚ₁ bs≡) (mk&ₚ  none sndₚ₂ refl) =
    ⊥-elim (nc bs≡' x sndₚ₂)
    where
    @0 bs≡' : bs₁ ++ bs₂ ++ [] ≡ xs ++ []
    bs≡' = begin (bs₁ ++ bs₂ ++ [] ≡⟨ solve (++-monoid Σ) ⟩
                 bs₁ ++ bs₂ ≡⟨ sym bs≡ ⟩
                 xs ≡⟨ solve (++-monoid Σ) ⟩
                 xs ++ [] ∎)
  unambiguous-option₁&₁ ua₁ nn₁ ua₂ nc (mk&ₚ (some x) sndₚ₁ bs≡) (mk&ₚ (some x₁) sndₚ₂ bs≡₁) =
    cong (λ where (mk&ₚ v₀ v₁ eq) → mk&ₚ (some v₀) v₁ eq ) (‼ pf)
    where
    @0 pf : mk&ₚ x sndₚ₁ bs≡ ≡ mk&ₚ x₁ sndₚ₂ bs≡₁
    pf = unambiguous&ₚ ua₁ nn₁ ua₂ (mk&ₚ x sndₚ₁ bs≡) (mk&ₚ x₁ sndₚ₂ bs≡₁)

  unambiguous-&₁option₁ : ∀ {@0 A B} → Unambiguous A → NonNesting A → Unambiguous B → NonEmpty B → Unambiguous (&ₚ A (Option B))
  unambiguous-&₁option₁{A}{B} ua₁ nn₁ ua₂ nc (mk&ₚ{bs₁ = bs₁} fstₚ₁  none bs≡)    (mk&ₚ{bs₁ = bs₂} fstₚ₂  none bs≡₁) = ‼
    subst₀ (λ x → ∀ (fstₚ₂ : A x) bs≡₁ → mk&ₚ{A = A} fstₚ₁ none bs≡ ≡ mk&ₚ fstₚ₂ none bs≡₁)
      bs≡'
      (λ fstₚ₂ bs≡₁ →
        subst₂ (λ fstₚ₂ bs≡₁ → _ ≡ mk&ₚ fstₚ₂ none bs≡₁) (ua₁ fstₚ₁ fstₚ₂) (≡-unique bs≡ bs≡₁) refl)
      fstₚ₂ bs≡₁
    where
    @0 bs≡' : bs₁ ≡ bs₂
    bs≡' = ++-cancelʳ _ _ (trans₀ (sym bs≡) bs≡₁)
  unambiguous-&₁option₁ ua₁ nn₁ ua₂ nc (mk&ₚ{bs₁ = bs₁} fstₚ₁  none bs≡)    (mk&ₚ{bs₁ = bs₂}{bs₃} fstₚ₂ (some x) bs≡₁) =
    ⊥-elim (contradiction (Lemmas.++-cancel≡ˡ _ _ (nn₁ (sym bs≡') fstₚ₂ fstₚ₁) (sym bs≡')) (nc x))
    where
    @0 bs≡' : bs₁ ++ [] ≡ bs₂ ++ bs₃
    bs≡' = trans₀ (sym bs≡) bs≡₁
  unambiguous-&₁option₁ ua₁ nn₁ ua₂ nc (mk&ₚ{bs₁ = bs₂}{bs₃} fstₚ₁ (some x) bs≡) (mk&ₚ{bs₁ = bs₁} fstₚ₂  none bs≡₁) =
    ⊥-elim (contradiction (Lemmas.++-cancel≡ˡ _ _ (nn₁ (sym bs≡') fstₚ₁ fstₚ₂) (sym bs≡')) (nc x))
    where
    @0 bs≡' : bs₁ ++ [] ≡ bs₂ ++ bs₃
    bs≡' = trans₀ (sym bs≡₁) bs≡
  unambiguous-&₁option₁ ua₁ nn₁ ua₂ nc (mk&ₚ fstₚ₁ (some x) bs≡) (mk&ₚ fstₚ₂ (some x₁) bs≡₁) =
    cong (λ where (mk&ₚ x y bs≡) → mk&ₚ x (some y) bs≡) (unambiguous&ₚ ua₁ nn₁ ua₂ (mk&ₚ fstₚ₁ x bs≡) (mk&ₚ fstₚ₂ x₁ bs≡₁))

  option₂&₁ : ∀ {@0 A B} → Unambiguous A → NonNesting A → NonEmpty A → Unambiguous B → NonEmpty B → NoConfusion A B → Unambiguous (&ₚ (Option A) (Option B))
  option₂&₁{A}{B} ua₁ nn₁ ne₁ ua₂ ne₂ nc (mk&ₚ{bs₂ = bs₁} none sndₚ₁ bs≡) (mk&ₚ{bs₂ = bs₂} none sndₚ₂ bs≡₁) =
    subst₀ (λ bs → ∀ (sndₚ₂ : Option B bs) (@0 bs≡₁ : _ ≡ bs) → _ ≡ mk&ₚ _ sndₚ₂ bs≡₁)
      bs≡'
      (λ sndₚ₂ bs≡₁ → ‼
        subst₂ (λ sndₚ₂ bs≡₁ → _ ≡ mk&ₚ none sndₚ₂ bs≡₁) (option₁{B} ua₂ ne₂ sndₚ₁ sndₚ₂) (‼ ≡-unique bs≡ bs≡₁)
          refl)
      sndₚ₂ bs≡₁
    where
    @0 bs≡' : bs₁ ≡ bs₂
    bs≡' = trans₀ (sym bs≡) bs≡₁
  option₂&₁ ua₁ nn₁ ne₁ ua₂ ne₂ nc (mk&ₚ none none refl) (mk&ₚ{bs₁ = bs₂}{bs₃} (some x) sndₚ₂ bs≡₁) =
    contradiction bs≡' (ne₁ x)
    where
    @0 bs≡' : bs₂ ≡ []
    bs≡' = ++-conicalˡ _ _ (sym bs≡₁)
  option₂&₁ ua₁ nn₁ ne₁ ua₂ ne₂ nc (mk&ₚ{bs₂ = bs₁} none (some x₁) bs≡) (mk&ₚ{bs₁ = bs₂}{bs₃} (some x) sndₚ₂ bs≡₁) =
    contradiction x₁ (nc bs≡' x)
    where
    @0 bs≡' : bs₂ ++ bs₃ ≡ bs₁ ++ []
    bs≡' = trans₀ (sym bs≡₁) (trans₀ bs≡ (solve (++-monoid Σ)))
  option₂&₁ ua₁ nn₁ ne₁ ua₂ ne₂ nc (mk&ₚ{bs₁ = bs₁}{bs₂} (some x) sndₚ₁ bs≡) (mk&ₚ none none refl) =
    contradiction (++-conicalˡ _ _ (sym bs≡)) (ne₁ x)
  option₂&₁ ua₁ nn₁ ne₁ ua₂ ne₂ nc (mk&ₚ{bs₁ = bs₁}{bs₂} (some x) sndₚ₁ bs≡) (mk&ₚ{bs₂ = bs₃} none (some x₁) bs≡₁) =
    contradiction x₁ (nc (trans₀ bs≡' (bs₃ ≡ bs₃ ++ [] ∋ solve (++-monoid Σ))) x)
    where
    @0 bs≡' : bs₁ ++ bs₂ ≡ [] ++ bs₃
    bs≡' = trans₀ (sym bs≡) bs≡₁
  option₂&₁ ua₁ nn₁ ne₁ ua₂ ne₂ nc (mk&ₚ (some x) sndₚ₁ bs≡) (mk&ₚ (some x₁) sndₚ₂ bs≡₁) =
    cong (λ where (mk&ₚ x y eq) → mk&ₚ (some x) y eq)
      (unambiguous-&₁option₁ ua₁ nn₁ ua₂ ne₂ (mk&ₚ x sndₚ₁ bs≡) (mk&ₚ x₁ sndₚ₂ bs≡₁))

  @0 option₃&₂ : ∀ {@0 A B C} → Unambiguous A → NonNesting A →  NonEmpty A → Unambiguous B → NonNesting B → NonEmpty B → Unambiguous C → NonEmpty C → NoConfusion A B → NoConfusion A C → NoConfusion B C → Unambiguous (&ₚ (Option A) (&ₚ (Option B) (Option C)))
  option₃&₂ ua₁ nn₁ ne₁ ua₂ nn₂ ne₂ ua₃ ne₃ nc₁ nc₂ nc₃ (mk&ₚ none v₁ refl) (mk&ₚ none v₁' refl) =
    cong (λ x → mk&ₚ none x refl) (option₂&₁ ua₂ nn₂ ne₂ ua₃ ne₃ nc₃ v₁ v₁')
  option₃&₂ ua₁ nn₁ ne₁ ua₂ nn₂ ne₂ ua₃ ne₃ nc₁ nc₂ nc₃ (mk&ₚ none (mk&ₚ{bs₁ = bs₁}{bs₂} (some v₂) v₃ bs≡) refl) (mk&ₚ{bs₁ = bs₁'}{bs₂'} (some x) (mk&ₚ v₂' v₃' refl) bs≡') =
    contradiction v₂ (nc₁ (sym bs≡“) x)
    where
    @0 bs≡“ : bs₁ ++ bs₂ ≡ bs₁' ++ bs₂'
    bs≡“ = trans₀ (sym bs≡) bs≡'
  option₃&₂ ua₁ nn₁ ne₁ ua₂ nn₂ ne₂ ua₃ ne₃ nc₁ nc₂ nc₃ (mk&ₚ none (mk&ₚ none none refl) refl) (mk&ₚ (some x) (mk&ₚ v₂' v₃' refl) bs≡') =
    contradiction (++-conicalˡ _ _ (sym bs≡')) (ne₁ x)
  option₃&₂ ua₁ nn₁ ne₁ ua₂ nn₂ ne₂ ua₃ ne₃ nc₁ nc₂ nc₃ (mk&ₚ none (mk&ₚ{bs₂ = bs₁} none (some v₃) refl) refl) (mk&ₚ{bs₁ = bs₁'}{bs₂'} (some x) (mk&ₚ v₂' v₃' refl) bs≡') =
    contradiction v₃ (nc₂ bs≡“ x)
    where
    @0 bs≡“ : bs₁' ++ bs₂' ≡ bs₁ ++ []
    bs≡“ = trans₀ (sym bs≡') (solve (++-monoid Σ))
  option₃&₂{A}{B}{C} ua₁ nn₁ ne₁ ua₂ nn₂ ne₂ ua₃ ne₃ nc₁ nc₂ nc₃ (mk&ₚ{bs₁ = bs₁}{bs₂} (some x) v bs≡) (mk&ₚ{bs₁ = bs₁'}{bs₂'} (some y) v' bs≡') = ‼
    subst₂ (λ bs₁' bs₂' → (y : A bs₁') (v' : &ₚ (Option B) (Option C) bs₂') (@0 bs≡' : _) → _ ≡ mk&ₚ{bs₁ = bs₁'}{bs₂'} (some y) v' bs≡')
      bs₁≡ bs₂≡
      (λ y v' bs≡' →
        subst₂ (λ y v' → _ ≡ mk&ₚ (some y) v' bs≡') (ua₁ x y) (option₂&₁ ua₂ nn₂ ne₂ ua₃ ne₃ nc₃ v v')
          (subst (λ bs≡' → _ ≡ mk&ₚ (some x) v bs≡') (≡-unique bs≡ bs≡') refl))
      y v' bs≡'
    where
    @0 bs≡“ : bs₁ ++ bs₂ ≡ bs₁' ++ bs₂'
    bs≡“ = trans₀ (sym bs≡) bs≡'

    @0 bs₁≡ : bs₁ ≡ bs₁'
    bs₁≡ = nn₁ bs≡“ x y

    @0 bs₂≡ : bs₂ ≡ bs₂'
    bs₂≡ = Lemmas.++-cancel≡ˡ _ _ bs₁≡ bs≡“
  option₃&₂ ua₁ nn₁ ne₁ ua₂ nn₂ ne₂ ua₃ ne₃ nc₁ nc₂ nc₃ (mk&ₚ{bs₁ = bs₁}{bs₂} (some x) v bs≡) (mk&ₚ{bs₁ = bs₁'}{bs₂'} none (mk&ₚ (some v₂') v₃' refl) bs≡') =
    contradiction v₂' (nc₁ bs≡“ x)
    where
    bs≡“ : bs₁ ++ bs₂ ≡ bs₁' ++ bs₂'
    bs≡“ = trans₀ (sym bs≡) bs≡'
  option₃&₂ ua₁ nn₁ ne₁ ua₂ nn₂ ne₂ ua₃ ne₃ nc₁ nc₂ nc₃ (mk&ₚ{bs₁ = bs₁}{bs₂} (some x) v bs≡) (mk&ₚ{bs₂ = bs₂'} none (mk&ₚ none (some v₃') refl) refl) =
    contradiction v₃' (nc₂ bs≡“ x)
    where
    bs≡“ : bs₁ ++ bs₂ ≡ bs₂' ++ []
    bs≡“ = trans₀ (sym bs≡) (solve (++-monoid Σ))
  option₃&₂ ua₁ nn₁ ne₁ ua₂ nn₂ ne₂ ua₃ ne₃ nc₁ nc₂ nc₃ (mk&ₚ (some x) (mk&ₚ v₂ v₃ refl) bs≡) (mk&ₚ none (mk&ₚ none none refl) refl) =
    contradiction (++-conicalˡ _ _ (sym bs≡)) (ne₁ x)


