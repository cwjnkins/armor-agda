{-# OPTIONS --subtyping #-}

import      Aeres.Grammar.Definitions.Eq
import      Aeres.Grammar.Definitions.NoSubstrings
import      Aeres.Grammar.Definitions.NonEmpty
import      Aeres.Grammar.Definitions.NonMalleable
import      Aeres.Grammar.Definitions.Unambiguous
import      Aeres.Grammar.Seq.TCB
open import Aeres.Prelude renaming (Σ to Sigma)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Grammar.Seq.Properties (Σ : Set) where

open Aeres.Grammar.Definitions.Eq           Σ
open Aeres.Grammar.Definitions.NoSubstrings Σ
open Aeres.Grammar.Definitions.NonEmpty     Σ
open Aeres.Grammar.Definitions.NonMalleable Σ
open Aeres.Grammar.Definitions.Unambiguous  Σ
open Aeres.Grammar.Seq.TCB                  Σ

@0 nonempty₁ : ∀ {A} {B : ∀ {bs} → A bs → List Σ → Set} → NonEmpty A → NonEmpty (&ₚᵈ A B)
nonempty₁ ne (mk&ₚ fstₚ₁ sndₚ₁ bs≡) refl = ne fstₚ₁ (++-conicalˡ _ _ (sym bs≡))

@0 nosubstringsᵈ
  : {A : List Σ → Set} {B : {@0 bs₁ : List Σ} → A bs₁ → List Σ → Set}
    → NoSubstrings A → Unambiguous A → (∀ {@0 bs} (a : A bs) → NoSubstrings (B a))
    → NoSubstrings (&ₚᵈ A B)
nosubstringsᵈ{A}{B} nnA uA nnB {xs₁}{ys₁}{xs₂}{ys₂}xs₁++ys₁≡xs₂++ys₂ (mk&ₚ{bs₁₁}{bs₂₁} fstₚ₁ sndₚ₁ bs≡) (mk&ₚ{bs₁₂}{bs₂₂} fstₚ₂ sndₚ₂ bs≡₁) =
  begin xs₁          ≡⟨ bs≡ ⟩
        bs₁₁ ++ bs₂₁ ≡⟨ cong₂ _++_ bs₁≡ bs₂≡ ⟩
        bs₁₂ ++ bs₂₂ ≡⟨ sym bs≡₁ ⟩
        xs₂          ∎
  where
  open ≡-Reasoning

  @0 xs++ys≡' : bs₁₁ ++ bs₂₁ ++ ys₁ ≡ bs₁₂ ++ bs₂₂ ++ ys₂
  xs++ys≡' = begin bs₁₁ ++ bs₂₁ ++ ys₁   ≡⟨ solve (++-monoid Σ) ⟩
                   (bs₁₁ ++ bs₂₁) ++ ys₁ ≡⟨ cong (_++ ys₁) (sym bs≡) ⟩
                   xs₁ ++ ys₁            ≡⟨ xs₁++ys₁≡xs₂++ys₂ ⟩
                   xs₂ ++ ys₂            ≡⟨ cong (_++ ys₂) bs≡₁ ⟩
                   (bs₁₂ ++ bs₂₂) ++ ys₂ ≡⟨ solve (++-monoid Σ) ⟩
                   bs₁₂ ++ bs₂₂ ++ ys₂   ∎

  @0 bs₁≡ : bs₁₁ ≡ bs₁₂
  bs₁≡ = nnA xs++ys≡' fstₚ₁ fstₚ₂

  fstₚ≡ : fstₚ₁ ≡ subst A (sym bs₁≡) fstₚ₂
  fstₚ≡ = uA fstₚ₁ _

  B≡ : B fstₚ₁ bs₂₂ ≡ B fstₚ₂ bs₂₂
  B≡ = begin B fstₚ₁ bs₂₂ ≡⟨ cong (λ x → B x bs₂₂) fstₚ≡ ⟩
             B (subst A (sym bs₁≡) fstₚ₂) bs₂₂ ≡⟨ ≡-elim (λ {y} e → B (subst A e fstₚ₂) bs₂₂ ≡ B _ bs₂₂) refl (sym bs₁≡) ⟩
             B fstₚ₂ bs₂₂ ∎

  sndₚ₂' : B fstₚ₁ bs₂₂
  sndₚ₂' = subst {A = Set} id (sym B≡) sndₚ₂

  @0 bs₂≡ : bs₂₁ ≡ bs₂₂
  bs₂≡ = nnB fstₚ₁ (Lemmas.++-cancel≡ˡ _ _ bs₁≡ xs++ys≡') sndₚ₁ sndₚ₂'

@0 nosubstrings : ∀ {A B} → NoSubstrings A → NoSubstrings B → NoSubstrings (&ₚ A B)
nosubstrings nnA nnB {xs₁}{ys₁}{xs₂}{ys₂} xs++ys≡ (mk&ₚ{bs₁₁}{bs₂₁} a₁ b₁ bs≡) (mk&ₚ{bs₁₂}{bs₂₂} a₂ b₂ bs≡₁) =
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

@0 unambiguousᵈ
  : ∀ {A} {B : ∀ {bs} → A bs → List Σ → Set} → Unambiguous A → NoSubstrings A
    → (∀ {@0 bs} (a : A bs) → Unambiguous (B a))
    → Unambiguous (&ₚᵈ A B)
unambiguousᵈ{A}{B} ua nna ub (mk&ₚ{bs₁₁}{bs₂₁} fstₚ₁ sndₚ₁ bs≡) (mk&ₚ{bs₁₂}{bs₂₂} fstₚ₂ sndₚ₂ bs≡₁) =
  let @0 bs≡' : bs₁₁ ++ bs₂₁ ≡ bs₁₂ ++ bs₂₂
      bs≡' = trans (sym bs≡) bs≡₁
  in
  case nna bs≡' fstₚ₁ fstₚ₂ of λ where
    refl →
      case ‼ ua fstₚ₁ fstₚ₂ ret (const _) of λ where
        refl →
          case ‼ ++-cancelˡ bs₁₁ bs≡' ret (const _) of λ where
            refl →
              case ‼ ub fstₚ₁ sndₚ₁ sndₚ₂ ret (const _) of λ where
                refl →
                  case ‼ ≡-unique bs≡ bs≡₁ ret (const _) of λ where
                    refl → refl

@0 nonmalleableᵈ
  : ∀ {A} {B : ∀ {bs} → A bs → List Σ → Set} {ra : Raw A} {rb : Raw₁ ra B}
    → NonMalleable ra → NonMalleable₁ rb → NonMalleable (Raw&ₚ ra rb)
nonmalleableᵈ nm₁ nm₂ (mk&ₚ fstₚ₁ sndₚ₁ refl) (mk&ₚ fstₚ₂ sndₚ₂ refl) eq =
  case Inverse.f⁻¹ Product.Σ-≡,≡↔≡ eq ret (const _) of λ where
    (fst≡ , snd≡) → case (nm₁ fstₚ₁ fstₚ₂ fst≡ ,′ singleton fst≡ refl) ret (const _) of λ where
      (refl , singleton refl refl) → case nm₂ sndₚ₁ sndₚ₂ snd≡ ret (const _) of λ where
        refl → refl
  where
  import Data.Product.Properties as Product

@0 unambiguous : ∀ {A B} → Unambiguous A → NoSubstrings A → Unambiguous B → Unambiguous (&ₚ A B)
unambiguous ua ns ub = unambiguousᵈ ua ns (λ _ → ub)

eq&ₚᵈ : ∀ {@0 A : @0 List Σ → Set} {@0 B : {@0 bs₁ : List Σ} → A bs₁ → @0 List Σ → Set}
        → Eq (Exists─ (List Σ) A)
        → (∀ {@0 bs₁} → (a : A bs₁) → Eq (Exists─ (List Σ) (B a)))
        → Eq (Exists─ (List Σ) (&ₚᵈ A B))
Eq._≟_ (eq&ₚᵈ eq₁ eq₂) (─ bs₁ , (mk&ₚ{bs₁₁}{bs₁₂} a₁ b₁ refl)) (─ bs₂ , mk&ₚ{bs₂₁}{bs₂₂} a₂ b₂ refl) =
  case Eq._≟_ eq₁ (─ bs₁₁ , a₁) (─ bs₂₁ , a₂) ret (const _) of λ where
    (no ¬p) → no λ where refl → contradiction refl ¬p
    (yes refl) →
      case Eq._≟_ (eq₂ a₁) (─ bs₁₂ , b₁) (─ bs₂₂ , b₂) ret (const _) of λ where
        (no ¬p) → no λ where refl → contradiction refl ¬p
        (yes refl) → yes refl

eq&ₚ : ∀ {@0 A B} → Eq (Exists─ (List Σ) A) → Eq (Exists─ (List Σ) B) → Eq (Exists─ (List Σ) (&ₚ A B))
Eq._≟_ (eq&ₚ eq₁ eq₂) (─ bs₁ , (mk&ₚ{bs₁₁}{bs₁₂} a₁ b₁ refl)) (─ bs₂ , mk&ₚ{bs₂₁}{bs₂₂} a₂ b₂ refl) =
  case Eq._≟_ eq₁ (─ bs₁₁ , a₁) (─ bs₂₁ , a₂) ret (const _) of λ where
    (no ¬p) → no λ where
      refl → contradiction refl ¬p
    (yes refl) → case Eq._≟_ eq₂ (─ bs₁₂ , b₁) (─ bs₂₂ , b₂) ret (const _) of λ where
      (no ¬p) → no λ where refl → contradiction refl ¬p
      (yes refl) → yes refl

eq≋&ₚ : ∀ {@0 A B} → Eq≋ A → Eq≋ B → Eq≋ (&ₚ A B)
eq≋&ₚ eq₁ eq₂ = Eq⇒Eq≋ (eq&ₚ (Eq≋⇒Eq eq₁) (Eq≋⇒Eq eq₂))

eq≋&ₚᵈ : ∀ {@0 A : @0 List Σ → Set} {@0 B : {@0 bs₁ : List Σ} → A bs₁ → @0 List Σ → Set}
         → Eq≋ A 
         → (∀ {@0 bs₁} → (a : A bs₁) → Eq≋ (B a))
         → Eq≋ (&ₚᵈ A B)
eq≋&ₚᵈ eq₁ eq₂ = Eq⇒Eq≋ (eq&ₚᵈ (Eq≋⇒Eq eq₁) (λ a → Eq≋⇒Eq (eq₂ a)))
