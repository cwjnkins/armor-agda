{-# OPTIONS --subtyping #-}

open import Aeres.Prelude
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Grammar.Definitions (Σ : Set) where

infix 4 _≋_
record _≋_ {@0 A : List Σ → Set} {@0 bs₁ bs₂} (a₁ : A bs₁) (a₂ : A bs₂) : Set where
  constructor mk≋
  field
    @0 bs≡ : bs₁ ≡ bs₂
    @0 a≡  : subst A bs≡ a₁ ≡ a₂

pattern ≋-refl = mk≋ refl refl

instance
  Irrel≋ : ∀ {@0 A bs₁ bs₂} {a₁ : A bs₁} {a₂ : A bs₂} → Irrel (_≋_{A} a₁ a₂)
  Irrel.irrel Irrel≋ ≋-refl = ≋-refl

Decidable-≋ : ((@0 _ : List Σ) → Set) → Set
Decidable-≋ A = ∀ {@0 bs₁ bs₂} (a₁ : A bs₁) (a₂ : A bs₂) → Dec (_≋_{A} a₁ a₂)

-- TODO: rename to "Unique"
Unambiguous : (A : List Σ → Set) → Set
Unambiguous A = ∀ {xs} → (a₁ a₂ : A xs) → a₁ ≡ a₂

unambiguousHet : ∀ {A} → Unambiguous A → ∀ {xs ys} → (eq : xs ≡ ys)
                 → (a₁ : A xs) (a₂ : A ys) → subst A eq a₁ ≡ a₂
unambiguousHet ua refl a₁ a₂ = ua a₁ a₂

-- TODO: rename to "Unambiguous"
NonNesting : (A : List Σ → Set) → Set
NonNesting A = ∀ {xs₁ ys₁ xs₂ ys₂} → xs₁ ++ ys₁ ≡ xs₂ ++ ys₂ → A xs₁ → A xs₂ → xs₁ ≡ xs₂

NonEmpty : (A : List Σ → Set) → Set
NonEmpty A = ∀ {xs : List Σ} → A xs → xs ≢ []

NoConfusion : (A B : List Σ → Set) → Set
NoConfusion A B = ∀ {xs₁ ys₁ xs₂ ys₂} → xs₁ ++ ys₁ ≡ xs₂ ++ ys₂
                  → (A xs₁ → ¬ B xs₂)

data Option (A : List Σ → Set) : (@0 _ : List Σ) → Set where
 none : Option A []
 some : ∀ {@0 xs} → A xs → Option A xs

isNone : ∀ {@0 A xs} →  Option A xs → Bool
isNone none = true
isNone (some _) = false

mapOption : ∀ {@0 A B} → (∀ {@0 xs} → A xs → B xs) → ∀ {@0 xs} → Option A xs → Option B xs
mapOption f none = none
mapOption f (some x) = some (f x)

record Σₚ (@0 A : List Σ → Set) (@0 B : (xs : List Σ) (a : A xs) → Set) (@0 xs : List Σ) : Set where
  constructor mk×ₚ
  field
    @0 {bs} : List Σ
    fstₚ : A bs
    sndₚ : B bs fstₚ
    @0 bs≡ : bs ≡ xs
open Σₚ public using (fstₚ ; sndₚ)

_×ₚ_ : (@0 A B : List Σ → Set) (@0 xs : List Σ) → Set
A ×ₚ B = Σₚ A (λ xs _ → B xs)

ExactLength : (@0 A : List Σ → Set) → ℕ → List Σ → Set
ExactLength A n = A ×ₚ ((_≡ n) ∘ length)

WithinLength : (@0 A : List Σ → Set) → ℕ → List Σ → Set
WithinLength A n = A ×ₚ ((_≤ n) ∘ length)

exactLength-nonnesting : ∀ {@0 A} {n} → NonNesting (ExactLength A n)
exactLength-nonnesting xs₁++ys₁≡xs₂++ys₂ (mk×ₚ fstₚ₁ sndₚ₁ refl) (mk×ₚ fstₚ₂ sndₚ₂ refl) =
  proj₁ $ Lemmas.length-++-≡ _ _ _ _ xs₁++ys₁≡xs₂++ys₂ (trans sndₚ₁ (sym sndₚ₂))

withinLength-nonnesting : ∀ {@0 A} {n} → NonNesting A → NonNesting (WithinLength A n)
withinLength-nonnesting nn ++≡ (mk×ₚ fstₚ₁ sndₚ₁ refl) (mk×ₚ fstₚ₂ sndₚ₂ refl) =
  nn ++≡ fstₚ₁ fstₚ₂

withinLength-noconfusion₁ : ∀ {@0 A B} {n} → NoConfusion A B → NoConfusion (WithinLength A n) B
withinLength-noconfusion₁ nc ++≡ (mk×ₚ fstₚ₁ sndₚ₁ refl) = nc ++≡ fstₚ₁

record &ₚ (@0 A B : List Σ → Set) (@0 bs : List Σ) : Set where
  constructor mk&ₚ
  field
    @0 {bs₁ bs₂} : List Σ
    fstₚ : A bs₁
    sndₚ : B bs₂
    @0 bs≡ : bs ≡ bs₁ ++ bs₂
open &ₚ public using (fstₚ ; sndₚ)

@0 NonNesting&ₚ : {A B : List Σ → Set} → NonNesting A → NonNesting B → NonNesting (&ₚ A B)
NonNesting&ₚ nnA nnB {xs₁}{ys₁}{xs₂}{ys₂} xs++ys≡ (mk&ₚ{bs₁₁}{bs₂₁} a₁ b₁ bs≡) (mk&ₚ{bs₁₂}{bs₂₂} a₂ b₂ bs≡₁) =
  begin xs₁          ≡⟨ bs≡ ⟩
        bs₁₁ ++ bs₂₁ ≡⟨ cong (_++ bs₂₁) bs₁≡ ⟩
        bs₁₂ ++ bs₂₁ ≡⟨ cong (bs₁₂ ++_) bs₂≡ ⟩
        bs₁₂ ++ bs₂₂ ≡⟨ sym bs≡₁ ⟩
        xs₂          ∎
  where
  open ≡-Reasoning

  @0 xs++ys≡' : bs₁₁ ++ bs₂₁ ++ ys₁ ≡ bs₁₂ ++ bs₂₂ ++ ys₂
  xs++ys≡' = begin bs₁₁ ++ bs₂₁ ++ ys₁   ≡⟨ solve (++-monoid Σ) ⟩
                   (bs₁₁ ++ bs₂₁) ++ ys₁ ≡⟨ cong (_++ ys₁) (sym bs≡) ⟩
                   xs₁ ++ ys₁            ≡⟨ xs++ys≡ ⟩
                   xs₂ ++ ys₂            ≡⟨ cong (_++ ys₂) bs≡₁ ⟩
                   (bs₁₂ ++ bs₂₂) ++ ys₂ ≡⟨ solve (++-monoid Σ) ⟩
                   bs₁₂ ++ bs₂₂ ++ ys₂   ∎

  @0 bs₁≡ : bs₁₁ ≡ bs₁₂
  bs₁≡ = nnA xs++ys≡' a₁ a₂

  @0 bs₂≡ : bs₂₁ ≡ bs₂₂
  bs₂≡ = nnB (++-cancelˡ bs₁₁ (trans xs++ys≡' (cong (_++ bs₂₂ ++ ys₂) (sym bs₁≡)))) b₁ b₂
