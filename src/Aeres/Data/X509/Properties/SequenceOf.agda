{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Sum
import      Aeres.Data.X509.Properties.Length as LengthProps
open import Aeres.Prelude
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Properties.SequenceOf where

open Base256
open Aeres.Grammar.Definitions Dig
open Aeres.Grammar.Properties  Dig
open Aeres.Grammar.Sum         Dig

module SequenceOf where
  equivalent : ∀ {@0 A} → Equivalent (Sum (Option (const ⊥)) (&ₚ A (Generic.SequenceOf A))) (Generic.SequenceOf A)
  proj₁ equivalent (Sum.inj₁ none) = Generic.nil
  proj₁ equivalent (Sum.inj₂ (mk&ₚ fstₚ₁ sndₚ₁ bs≡)) =
    Generic.cons (Generic.mkSequenceOf fstₚ₁ sndₚ₁ bs≡)
  proj₂ equivalent Generic.nil = inj₁ none
  proj₂ equivalent (Generic.cons (Generic.mkSequenceOf h t bs≡)) =
    inj₂ (mk&ₚ h t bs≡)

  iso : ∀ {@0 A} → Iso (Sum (Option (const ⊥)) (&ₚ A (Generic.SequenceOf A))) (Generic.SequenceOf A)
  proj₁ iso = equivalent
  proj₁ (proj₂ iso) (Sum.inj₁ none) = refl
  proj₁ (proj₂ iso) (Sum.inj₂ (mk&ₚ fstₚ₁ sndₚ₁ bs≡)) = refl
  proj₂ (proj₂ iso) Generic.nil = refl
  proj₂ (proj₂ iso) (Generic.cons (Generic.mkSequenceOf h t bs≡)) = refl

  @0 nonempty : ∀ {@0 A n} → NonEmpty A → NonEmpty (Generic.BoundedSequenceOf A (suc n))
  nonempty ne (mk×ₚ (Generic.cons (Generic.mkSequenceOf h t bs≡)) sndₚ₁ refl) refl =
    ne h (++-conicalˡ _ _ (sym bs≡))

  @0 unambiguous : ∀ {@0 A} → Unambiguous A → NonEmpty A → NonNesting A → Unambiguous (Generic.SequenceOf A)
  unambiguous ua ne nn Generic.nil Generic.nil = refl
  unambiguous ua ne nn{xs} Generic.nil (Generic.cons (Generic.mkSequenceOf{bs₁}{bs₂} h t bs≡)) =
    contradiction (++-conicalˡ _ _ (sym bs≡)) (ne h)
  unambiguous ua ne nn {xs} (Generic.cons (Generic.mkSequenceOf h t bs≡)) Generic.nil =
    contradiction (++-conicalˡ _ _ (sym bs≡)) (ne h)
  unambiguous ua ne nn (Generic.cons (Generic.mkSequenceOf{bs₁ = bs₁₁}{bs₁₂} h t bs≡)) (Generic.cons (Generic.mkSequenceOf{bs₁ = bs₂₁}{bs₂₂} h₁ t₁ bs≡₁)) =
    ≡-elim (λ {bs₂₁} bs₁≡ → ∀ h₁ bs≡₁ → _ ≡ Generic.cons (Generic.mkSequenceOf {bs₁ = bs₂₁} h₁ t₁ bs≡₁))
      (λ h₁ bs≡₁ →
        ≡-elim (λ {bs₂₂} bs₂≡ → ∀ t₁ bs≡₁ → _ ≡ Generic.cons (Generic.mkSequenceOf{bs₂ = bs₂₂} h₁ t₁ bs≡₁))
          (λ t₁ bs≡₁ →
            subst₂ (λ x y → _ ≡ Generic.cons (Generic.mkSequenceOf x y bs≡₁)) (ua h h₁) (unambiguous ua ne nn t t₁)
              (subst₀ (λ x → _ ≡ Generic.cons (Generic.mkSequenceOf _ _ x)) (≡-unique bs≡ bs≡₁) refl))
          bs₂≡ t₁ bs≡₁)
      bs₁≡ h₁ bs≡₁
    where
    @0 bs≡' : bs₁₁ ++ bs₁₂ ≡ bs₂₁ ++ bs₂₂
    bs≡' = trans₀ (sym bs≡) bs≡₁

    @0 bs₁≡ : bs₁₁ ≡ bs₂₁
    bs₁≡ = nn bs≡' h h₁

    bs₂≡ : bs₁₂ ≡ bs₂₂
    bs₂≡ = Lemmas.++-cancel≡ˡ _ _ bs₁≡ bs≡'

  @0 sameLength : ∀ {@0 A bs} → NonNesting A → NonEmpty A → (s₁ s₂ : Generic.SequenceOf A bs) → Generic.lengthSequence s₁ ≡ Generic.lengthSequence s₂
  sameLength nn ne Generic.nil Generic.nil = refl
  sameLength nn ne Generic.nil (Generic.cons (Generic.mkSequenceOf h t bs≡)) =
    contradiction
      (++-conicalˡ _ _ (sym bs≡))
      (ne h)
  sameLength nn ne (Generic.cons (Generic.mkSequenceOf h t bs≡)) Generic.nil =
    contradiction
      (++-conicalˡ _ _ (sym bs≡))
      (ne h)
  sameLength nn ne (Generic.cons (Generic.mkSequenceOf{bs₁₁}{bs₁₂} h t bs≡)) (Generic.cons (Generic.mkSequenceOf{bs₂₁}{bs₂₂} h₁ t₁ bs≡₁)) =
    cong suc (trans₀ ih lem)
    where
    @0 bs₁≡ : bs₁₁ ≡ bs₂₁
    bs₁≡ = nn (trans₀ (sym bs≡) bs≡₁) h h₁

    @0 bs₂≡ : bs₁₂ ≡ bs₂₂
    bs₂≡ = proj₂ (Lemmas.length-++-≡ _ _ _ _ ((trans₀ (sym bs≡) bs≡₁)) (cong length bs₁≡))

    t₁' : Generic.SequenceOf _ bs₁₂
    t₁' = subst₀ (Generic.SequenceOf _) (sym bs₂≡) t₁

    ih : Generic.lengthSequence t ≡ Generic.lengthSequence t₁'
    ih = sameLength nn ne t t₁'

    @0 lem : Generic.lengthSequence t₁' ≡ Generic.lengthSequence t₁
    lem =
      ≡-elim
        (λ {ys} eq → ∀ (t' : Generic.SequenceOf _ ys) → Generic.lengthSequence (subst₀ _ (sym eq) t') ≡ Generic.lengthSequence t')
        (λ t → refl) bs₂≡ t₁

module BoundedSequenceOf where

  @0 unambiguous : ∀ {@0 A n} → Unambiguous A → NonEmpty A → NonNesting A → Unambiguous (Generic.BoundedSequenceOf A n)
  unambiguous uaₐ naₐ nnₐ =
    unambiguousΣₚ (SequenceOf.unambiguous uaₐ naₐ nnₐ)
      λ {xs} a → ≤-irrelevant

  postulate
    instance
      BoundedSequenceOfEq≋ : ∀ {@0 A : @0 List Dig → Set} ⦃ _ : Eq≋ A ⦄ → ∀ {@0 n} → Eq≋ (Generic.BoundedSequenceOf A n)

open SequenceOf public
