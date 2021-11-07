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

symNoConfusion : ∀ {@0 A B} → NoConfusion A B → NoConfusion B A
symNoConfusion nc ++≡ v₂ v₁ = nc (sym ++≡) v₁ v₂

Equivalent : (A B : (@0 _ : List Σ) → Set) → Set
Equivalent A B = (∀ {@0 xs} → A xs → B xs) × (∀ {@0 xs} → B xs → A xs)

symEquivalent : ∀ {A B} → Equivalent A B → Equivalent B A
symEquivalent (fst , snd) = snd , fst

transEquivalent : ∀ {A B C} → Equivalent A B → Equivalent B C → Equivalent A C
proj₁ (transEquivalent e₁ e₂) = proj₁ e₂ ∘ proj₁ e₁
proj₂ (transEquivalent e₁ e₂) = proj₂ e₁ ∘ proj₂ e₂

data Option (@0 A : List Σ → Set) : (@0 _ : List Σ) → Set where
 none : Option A []
 some : ∀ {@0 xs} → A xs → Option A xs

isNone : ∀ {@0 A xs} →  Option A xs → Bool
isNone none = true
isNone (some _) = false

mapOption : ∀ {@0 A B} → (∀ {@0 xs} → A xs → B xs) → ∀ {@0 xs} → Option A xs → Option B xs
mapOption f none = none
mapOption f (some x) = some (f x)

mapOptionK : ∀ {@0 A B xs} → (A xs → B xs) → Option A xs → Option B xs
mapOptionK f none = none
mapOptionK f (some x) = some (f x)

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

noconfusion×ₚ₁ : ∀ {@0 A₁ A₂ B} → NoConfusion A₁ A₂ → NoConfusion (A₁ ×ₚ B) A₂
noconfusion×ₚ₁ nc ++≡ (mk×ₚ fstₚ₁ sndₚ₁ refl) y = nc ++≡ fstₚ₁ y

nonnesting×ₚ₁ : ∀ {@0 A B} → NonNesting A → NonNesting (A ×ₚ B)
nonnesting×ₚ₁ nn ++≡ (mk×ₚ fstₚ₁ _ refl) (mk×ₚ fstₚ₂ _ refl) = nn ++≡ fstₚ₁ fstₚ₂

unambiguous×ₚ : ∀ {@0 A B} → Unambiguous A → Unambiguous B → Unambiguous (A ×ₚ B)
unambiguous×ₚ ua₁ ua₂ (mk×ₚ fstₚ₁ sndₚ₁ refl) (mk×ₚ fstₚ₂ sndₚ₂ refl) =
  subst₀ (λ x → mk×ₚ fstₚ₁ sndₚ₁ refl ≡ mk×ₚ x sndₚ₂ refl) (ua₁ fstₚ₁ fstₚ₂)
    (subst₀ (λ x → mk×ₚ fstₚ₁ sndₚ₁ refl ≡ mk×ₚ fstₚ₁ x refl) (ua₂ sndₚ₁ sndₚ₂)
      refl)

map×ₚ : ∀ {@0 A₁ A₂ B} → (∀ {@0 xs} → A₁ xs → A₂ xs) → (∀ {@0 xs} → (A₁ ×ₚ B) xs → (A₂ ×ₚ B) xs)
map×ₚ f (mk×ₚ fstₚ₁ sndₚ₁ bs≡) = mk×ₚ (f fstₚ₁) sndₚ₁ bs≡

equivalent×ₚ : ∀ {@0 A₁ A₂ B} → Equivalent A₁ A₂ → Equivalent (A₁ ×ₚ B) (A₂ ×ₚ B)
proj₁ (equivalent×ₚ (f , g)) = map×ₚ f
proj₂ (equivalent×ₚ (f , g)) = map×ₚ g

ExactLength : (@0 A : List Σ → Set) → ℕ → (@0 _ : List Σ) → Set
ExactLength A n = A ×ₚ (Erased ∘ (_≡ n) ∘ length)

WithinLength : (@0 A : List Σ → Set) → ℕ → (@0 _ : List Σ) → Set
WithinLength A n = A ×ₚ (Erased ∘ (_≤ n) ∘ length)

projectWithinLength : ∀ {@0 A xs} {n} → WithinLength A n xs → A xs
projectWithinLength (mk×ₚ fstₚ₁ sndₚ₁ refl) = fstₚ₁

exactLength-nonnesting : ∀ {@0 A} {n} → NonNesting (ExactLength A n)
exactLength-nonnesting xs₁++ys₁≡xs₂++ys₂ (mk×ₚ fstₚ₁ (─ sndₚ₁) refl) (mk×ₚ fstₚ₂ (─ sndₚ₂) refl) =
  proj₁ $ Lemmas.length-++-≡ _ _ _ _ xs₁++ys₁≡xs₂++ys₂ (trans₀ sndₚ₁ (sym sndₚ₂))

withinLength-nonnesting : ∀ {@0 A} {n} → NonNesting A → NonNesting (WithinLength A n)
withinLength-nonnesting nn ++≡ (mk×ₚ fstₚ₁ sndₚ₁ refl) (mk×ₚ fstₚ₂ sndₚ₂ refl) =
  nn ++≡ fstₚ₁ fstₚ₂

withinLength-noconfusion₁ : ∀ {@0 A B} {n} → NoConfusion A B → NoConfusion (WithinLength A n) B
withinLength-noconfusion₁ nc ++≡ (mk×ₚ fstₚ₁ sndₚ₁ refl) = nc ++≡ fstₚ₁

withinLength-unambiguous : ∀ {@0 A} {n} → Unambiguous A → Unambiguous (WithinLength A n)
withinLength-unambiguous ua (mk×ₚ fstₚ₁ (─ sndₚ₁) refl) (mk×ₚ fstₚ₂ (─ sndₚ₂) refl) =
  subst₀ (λ x → mk×ₚ fstₚ₁ (─ sndₚ₁) refl ≡ mk×ₚ x (─ sndₚ₂) refl) (ua fstₚ₁ fstₚ₂)
    (subst₀ (λ x → mk×ₚ fstₚ₁ (─ sndₚ₁) refl ≡ mk×ₚ fstₚ₁ (─ x) refl) (‼ ≤-irrelevant sndₚ₁ sndₚ₂)
       refl)
  where open import Data.Nat.Properties

record &ₚᵈ (@0 A : List Σ → Set) (@0 B : (@0 bs₁ : List Σ) → A bs₁ → List Σ → Set) (@0 bs : List Σ) : Set where
  constructor mk&ₚ
  field
    @0 {bs₁ bs₂} : List Σ
    fstₚ : A bs₁
    sndₚ : B bs₁ fstₚ bs₂
    @0 bs≡ : bs ≡ bs₁ ++ bs₂
open &ₚᵈ public using (fstₚ ; sndₚ)

&ₚ : (@0 A B : List Σ → Set) (@0 bs : List Σ) → Set
&ₚ A B = &ₚᵈ A λ _ _ → B

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

unambiguous&ₚ : ∀ {@0 A B} → Unambiguous A → NonNesting A → Unambiguous B → NonNesting B → Unambiguous (&ₚ A B)
unambiguous&ₚ{A}{B} ua₁ nn₁ ua₂ nn₂ (mk&ₚ{bs₁ = bs₁₁}{bs₁₂} fstₚ₁ sndₚ₁ bs≡) (mk&ₚ{bs₁ = bs₂₁}{bs₂₂} fstₚ₂ sndₚ₂ bs≡₁) =
  ‼ ≡-elim (λ {bs₁} _ → ∀ fstₚ bs≡₁ → mk&ₚ fstₚ₁ sndₚ₁ bs≡ ≡ mk&ₚ{bs₁ = bs₁} fstₚ sndₚ₂ bs≡₁)
    (λ fstₚ₂' bs≡₂' →
      ‼ ≡-elim (λ {bs₂} _ → (sndₚ : B bs₂) (bs≡₂ : _ ≡ bs₁₁ ++ bs₂) → mk&ₚ fstₚ₁ sndₚ₁ bs≡ ≡ mk&ₚ{bs₂ = bs₂} fstₚ₂' sndₚ bs≡₂ )
        (λ sndₚ₂' bs≡₂' →
          subst₂ (λ x y → mk&ₚ fstₚ₁ sndₚ₁ bs≡ ≡ mk&ₚ x y bs≡₂') (ua₁ fstₚ₁ fstₚ₂') (ua₂ sndₚ₁ sndₚ₂')
            (subst (λ x → mk&ₚ fstₚ₁ sndₚ₁ bs≡ ≡ mk&ₚ fstₚ₁ sndₚ₁ x) (≡-unique bs≡ bs≡₂') refl))
        bs₂≡ sndₚ₂ bs≡₂')
    bs₁≡ fstₚ₂ bs≡₁
  where
  open ≡-Reasoning

  @0 bs₁≡ : bs₁₁ ≡ bs₂₁
  bs₁≡ = nn₁ (trans₀ (sym bs≡) bs≡₁) fstₚ₁ fstₚ₂

  @0 fstₚ≡ : subst A bs₁≡ fstₚ₁ ≡ fstₚ₂
  fstₚ≡ = ≡-elim (λ {y} eq → ∀ fstₚ₂ → subst A eq fstₚ₁ ≡ fstₚ₂) (ua₁ fstₚ₁) bs₁≡ fstₚ₂

  @0 ++≡ : bs₁₁ ++ bs₁₂ ++ [] ≡ bs₂₁ ++ bs₂₂ ++ []
  ++≡ = begin (bs₁₁ ++ bs₁₂ ++ [] ≡⟨ solve (++-monoid Σ) ⟩
              bs₁₁ ++ bs₁₂ ≡⟨ trans₀ (sym bs≡) bs≡₁ ⟩
              bs₂₁ ++ bs₂₂ ≡⟨ solve (++-monoid Σ) ⟩
               bs₂₁ ++ bs₂₂ ++ [] ∎)

  @0 bs₂≡ : bs₁₂ ≡ bs₂₂
  bs₂≡ = nn₂{ys₁ = []}{ys₂ = []} (Lemmas.++-cancel≡ˡ _ _ bs₁≡ ++≡) sndₚ₁ sndₚ₂
