{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.IList
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Sum
import      Aeres.Data.X509.Properties.Length as LengthProps
open import Aeres.Prelude
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Properties.SequenceOf where

open Base256
open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.IList       UInt8
open Aeres.Grammar.Properties  UInt8
open Aeres.Grammar.Sum         UInt8

module SequenceOf where
  equivalent : ∀ {@0 A} → Equivalent (Sum (Option (const ⊥)) (&ₚ A (SequenceOf A))) (SequenceOf A)
  proj₁ equivalent (Sum.inj₁ none) = nil
  proj₁ equivalent (Sum.inj₂ (mk&ₚ fstₚ₁ sndₚ₁ bs≡)) =
    consSequenceOf fstₚ₁ sndₚ₁ bs≡
  proj₂ equivalent nil = inj₁ none
  proj₂ equivalent (cons (mkSequenceOf h t bs≡)) =
    inj₂ (mk&ₚ h t bs≡)

  iso : ∀ {@0 A} → Iso (Sum (Option (const ⊥)) (&ₚ A (SequenceOf A))) (SequenceOf A)
  proj₁ iso = equivalent
  proj₁ (proj₂ iso) (Sum.inj₁ none) = refl
  proj₁ (proj₂ iso) (Sum.inj₂ (mk&ₚ fstₚ₁ sndₚ₁ bs≡)) = refl
  proj₂ (proj₂ iso) nil = refl
  proj₂ (proj₂ iso) (cons (mkSequenceOf h t bs≡)) = refl

  @0 nonempty : ∀ {@0 A n} → NonEmpty A → NonEmpty (BoundedSequenceOf A (suc n))
  nonempty ne (mk×ₚ (cons (mkSequenceOf h t bs≡)) sndₚ₁ refl) refl =
    ne h (++-conicalˡ _ _ (sym bs≡))

  @0 unambiguous : ∀ {@0 A} → Unambiguous A → NonEmpty A → NonNesting A → Unambiguous (SequenceOf A)
  unambiguous ua ne nn nil nil = refl
  unambiguous ua ne nn{xs} nil (cons (mkSequenceOf{bs₁}{bs₂} h t bs≡)) =
    contradiction (++-conicalˡ _ _ (sym bs≡)) (ne h)
  unambiguous ua ne nn {xs} (cons (mkSequenceOf h t bs≡)) nil =
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

  @0 sameLength : ∀ {@0 A bs} → NonNesting A → NonEmpty A → (s₁ s₂ : SequenceOf A bs) → lengthSequence s₁ ≡ lengthSequence s₂
  sameLength nn ne nil nil = refl
  sameLength nn ne nil (cons (mkSequenceOf h t bs≡)) =
    contradiction
      (++-conicalˡ _ _ (sym bs≡))
      (ne h)
  sameLength nn ne (cons (mkSequenceOf h t bs≡)) nil =
    contradiction
      (++-conicalˡ _ _ (sym bs≡))
      (ne h)
  sameLength nn ne (cons (mkSequenceOf{bs₁₁}{bs₁₂} h t bs≡)) (cons (mkSequenceOf{bs₂₁}{bs₂₂} h₁ t₁ bs≡₁)) =
    cong suc (trans₀ ih lem)
    where
    @0 bs₁≡ : bs₁₁ ≡ bs₂₁
    bs₁≡ = nn (trans₀ (sym bs≡) bs≡₁) h h₁

    @0 bs₂≡ : bs₁₂ ≡ bs₂₂
    bs₂≡ = proj₂ (Lemmas.length-++-≡ _ _ _ _ ((trans₀ (sym bs≡) bs≡₁)) (cong length bs₁≡))

    t₁' : SequenceOf _ bs₁₂
    t₁' = subst₀ (SequenceOf _) (sym bs₂≡) t₁

    ih : lengthSequence t ≡ lengthSequence t₁'
    ih = sameLength nn ne t t₁'

    @0 lem : lengthSequence t₁' ≡ lengthSequence t₁
    lem =
      ≡-elim
        (λ {ys} eq → ∀ (t' : SequenceOf _ ys) → lengthSequence (subst₀ _ (sym eq) t') ≡ lengthSequence t')
        (λ t → refl) bs₂≡ t₁

module BoundedSequenceOf where

  @0 unambiguous : ∀ {@0 A n} → Unambiguous A → NonEmpty A → NonNesting A → Unambiguous (BoundedSequenceOf A n)
  unambiguous uaₐ naₐ nnₐ =
    unambiguousΣₚ (SequenceOf.unambiguous uaₐ naₐ nnₐ)
      λ {xs} a → ≤-irrelevant

open SequenceOf public

instance
    SequenceOfEq≋ : ∀ {@0 A : @0 List UInt8 → Set} ⦃ _ : Eq≋ A ⦄ → Eq≋ (SequenceOf A)
    Eq≋._≋?_ SequenceOfEq≋ {.[]} {.[]} nil nil = yes ≋-refl
    Eq≋._≋?_ SequenceOfEq≋ {.[]} {bs₂} nil (cons x) = no λ where (mk≋ refl ())
    Eq≋._≋?_ SequenceOfEq≋ {bs₁} {.[]} (cons x) nil = no λ where (mk≋ refl ())
    Eq≋._≋?_ SequenceOfEq≋ {bs₁} {bs₂} (cons v₁) (cons v₂)
      with IListCons.head v₁ ≋? IListCons.head v₂
    ... | yes ≋-refl
      with Eq≋._≋?_ SequenceOfEq≋ (IListCons.tail v₁) (IListCons.tail v₂)
    ... | yes ≋-refl
      with ‼ IListCons.bs≡ v₁
    ... | refl =
      yes (mk≋ (sym $ IListCons.bs≡ v₂)
            (‼ ≡-elim (λ {bs₂} bs₂≡ → (@0 bs≡ : bs₂ ≡ IListCons.bs₁ v₁ ++ _) →
              subst _ (sym bs₂≡) (cons (mkSequenceOf (IListCons.head v₂) (IListCons.tail v₂) bs≡)) ≡ cons v₂)
              (λ bs₂≡ → subst (λ x → cons (mkSequenceOf (IListCons.head v₂) (IListCons.tail v₂) x) ≡ cons v₂)
                (‼ (≡-unique (IListCons.bs≡ v₂) bs₂≡)) refl)
              (IListCons.bs≡ v₂) (IListCons.bs≡ v₁)))
    Eq≋._≋?_ SequenceOfEq≋ (cons v₁) (cons v₂) | yes ≋-refl | no ¬v₁≋v₂ = no λ where
      ≋-refl → contradiction ≋-refl ¬v₁≋v₂
    Eq≋._≋?_ SequenceOfEq≋ (cons v₁) (cons v₂) | no ¬v₁≋v₂ = no λ where
      ≋-refl → contradiction ≋-refl ¬v₁≋v₂

    BoundedSequenceOfEq≋ : ∀ {@0 A : @0 List UInt8 → Set} ⦃ _ : Eq≋ A ⦄ → ∀ {@0 n} → Eq≋ (BoundedSequenceOf A n)
    Eq≋._≋?_ BoundedSequenceOfEq≋{bs₁}{bs₂} v₁ v₂
      with fstₚ v₁ ≋? fstₚ v₂
    ... | yes ≋-refl
      with ‼ ≤-irrelevant (sndₚ v₁) (sndₚ v₂)
    ... | refl
      with ‼ Σₚ.bs≡ v₁
      |    ‼ Σₚ.bs≡ v₂
    ... | refl | refl = yes (mk≋ refl (subst (λ x → mk×ₚ _ _ x ≡ v₂) (≡-unique (Σₚ.bs≡ v₂) (Σₚ.bs≡ v₁)) refl))
    Eq≋._≋?_ BoundedSequenceOfEq≋{bs₁}{bs₂} v₁ v₂ | no ¬v₁≋v₂  = no λ where
      ≋-refl → contradiction ≋-refl ¬v₁≋v₂
