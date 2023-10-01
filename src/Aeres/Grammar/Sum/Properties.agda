{-# OPTIONS --subtyping #-}

open import Aeres.Prelude
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Sum.TCB
open import Data.Sum.Properties

module Aeres.Grammar.Sum.Properties (Σ : Set) where

open Aeres.Grammar.Sum.TCB     Σ
open Aeres.Grammar.Definitions Σ

nonempty : ∀ {@0 A B} → @0 NonEmpty A → @0 NonEmpty B → NonEmpty (Sum A B)
nonempty ne₁ ne₂ (inj₁ x) ≡[] = contradiction ≡[] (ne₁ x)
nonempty ne₁ ne₂ (inj₂ x) ≡[] = contradiction ≡[] (ne₂ x)

nosubstrings : ∀ {@0 A B} → @0 NoSubstrings A → @0 NoSubstrings B → NoConfusion A B → NoSubstrings (Sum A B)
nosubstrings nn₁ nn₂ nc ++≡ (inj₁ x) (inj₁ x₁) = ‼ nn₁ ++≡ x x₁
nosubstrings nn₁ nn₂ nc ++≡ (inj₁ x) (inj₂ x₁) = ⊥-elim (nc ++≡ x x₁)
nosubstrings nn₁ nn₂ nc ++≡ (inj₂ x) (inj₁ x₁) = ⊥-elim (nc (sym ++≡) x₁ x)
nosubstrings nn₁ nn₂ nc ++≡ (inj₂ x) (inj₂ x₁) = ‼ nn₂ ++≡ x x₁

-- TODO: rename
unambiguous' : ∀ {@0 A B} → @0 Unambiguous A → @0 Unambiguous B → @0 (∀ {xs} → A xs → ¬ B xs ) → Unambiguous (Sum A B)
unambiguous'{A} ua₁ ua₂ nc (inj₁ x) (inj₁ x₁) = ‼ cong Sum.inj₁ (ua₁ x x₁)
unambiguous' ua₁ ua₂ nc (inj₁ x) (inj₂ x₁) = ⊥-elim (nc x x₁)
unambiguous' ua₁ ua₂ nc (inj₂ x) (inj₁ x₁) = ⊥-elim (nc x₁ x)
unambiguous' ua₁ ua₂ nc (inj₂ x) (inj₂ x₁) = ‼ cong Sum.inj₂ (ua₂ x x₁)

@0 unambiguous : ∀ {@0 A B} → Unambiguous A → Unambiguous B → NoConfusion A B → Unambiguous (Sum A B)
unambiguous ua₁ ua₂ nc = unambiguous' ua₁ ua₂ λ {xs} → nc (refl {x = xs ++ []})

sumEq : ∀ {@0 A B : @0 List Σ → Set} → ⦃ _ : Eq (Exists─ (List Σ) A) ⦄ ⦃ _ : Eq (Exists─ (List Σ) B) ⦄
        → Eq (Exists─ (List Σ) (Sum A B))
Eq._≟_ sumEq (─ bs₁ , inj₁ x) (─ bs₂ , inj₁ x') =
  case (─ bs₁ ,e x) ≟ (─ bs₂ ,e x') ret (const _) of λ where
    (no ¬p) → no λ where refl → contradiction refl ¬p
    (yes refl) → yes refl
    
Eq._≟_ sumEq (─ bs₁ , inj₁ x) (─ bs₂ , inj₂ y) = no λ ()
Eq._≟_ sumEq (─ bs₁ , inj₂ x) (─ bs₂ , inj₁ y) = no λ ()
Eq._≟_ sumEq (─ bs₁ , inj₂ x) (─ bs₂ , inj₂ y) =
  case (─ bs₁ ,e x) ≟ (─ bs₂ ,e y) ret (const _) of λ where
    (no ¬p) → no λ where refl → contradiction refl ¬p
    (yes refl) → yes refl

sumEq≋ : ∀ {@0 A B : @0 List Σ → Set} → ⦃ eq₁ : Eq≋ A ⦄ → ⦃ eq₂ : Eq≋ B ⦄
         → Eq≋ (Sum A B)
sumEq≋ ⦃ eq₁ ⦄ ⦃ eq₂ ⦄ = Eq⇒Eq≋ (sumEq ⦃ Eq≋⇒Eq eq₁ ⦄ ⦃ Eq≋⇒Eq eq₂ ⦄)

@0 nonmalleable : ∀ {A B} {ra : Raw A} {rb : Raw B} → NonMalleable ra → NonMalleable rb → NonMalleable (RawSum ra rb)
nonmalleable x x₁ (inj₁ x₆) (inj₁ x₇) eq =
  case x _ _ (inj₁-injective eq)  of λ where
    refl → refl
nonmalleable x x₁ (inj₂ x₆) (inj₂ x₇) eq =
  case x₁ _ _ (inj₂-injective eq)  of λ where
    refl → refl
