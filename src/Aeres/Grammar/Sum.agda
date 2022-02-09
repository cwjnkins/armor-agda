{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

module Aeres.Grammar.Sum (Σ : Set) where

open import Aeres.Grammar.Definitions Σ

data Sum (@0 A B : List Σ → Set) : (@0 _ : List Σ) → Set where
  inj₁ : ∀ {@0 xs} → A xs → Sum A B xs
  inj₂ : ∀ {@0 xs} → B xs → Sum A B xs

nonemptySum : ∀ {@0 A B} → NonEmpty A → NonEmpty B → NonEmpty (Sum A B)
nonemptySum ne₁ ne₂ (inj₁ x) ≡[] = contradiction ≡[] (ne₁ x)
nonemptySum ne₁ ne₂ (inj₂ x) ≡[] = contradiction ≡[] (ne₂ x)

nonnestingSum : ∀ {@0 A B} → NonNesting A → NonNesting B → NoConfusion A B → NonNesting (Sum A B)
nonnestingSum nn₁ nn₂ nc ++≡ (inj₁ x) (inj₁ x₁) = nn₁ ++≡ x x₁
nonnestingSum nn₁ nn₂ nc ++≡ (inj₁ x) (inj₂ x₁) = ⊥-elim (nc ++≡ x x₁)
nonnestingSum nn₁ nn₂ nc ++≡ (inj₂ x) (inj₁ x₁) = ⊥-elim (nc (sym ++≡) x₁ x)
nonnestingSum nn₁ nn₂ nc ++≡ (inj₂ x) (inj₂ x₁) = nn₂ ++≡ x x₁

-- TODO: rename
@0 unambiguousSum' : ∀ {@0 A B} → Unambiguous A → Unambiguous B → (∀ {xs} → A xs → ¬ B xs ) → Unambiguous (Sum A B)
unambiguousSum'{A} ua₁ ua₂ nc (inj₁ x) (inj₁ x₁) = cong Sum.inj₁ (ua₁ x x₁)
unambiguousSum' ua₁ ua₂ nc (inj₁ x) (inj₂ x₁) = ⊥-elim (nc x x₁)
unambiguousSum' ua₁ ua₂ nc (inj₂ x) (inj₁ x₁) = ⊥-elim (nc x₁ x)
unambiguousSum' ua₁ ua₂ nc (inj₂ x) (inj₂ x₁) = cong Sum.inj₂ (ua₂ x x₁)

@0 unambiguousSum : ∀ {@0 A B} → Unambiguous A → Unambiguous B → NoConfusion A B → Unambiguous (Sum A B)
unambiguousSum ua₁ ua₂ nc = unambiguousSum' ua₁ ua₂ λ {xs} → nc (refl {x = xs ++ []})
