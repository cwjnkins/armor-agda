{-# OPTIONS --subtyping #-}

open import Aeres.Prelude
open import Aeres.Binary
open import Aeres.Data.X509
import Aeres.Data.X509.Properties.Length as LengthProps
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Properties.Seq where

open Base256
open import Aeres.Grammar.Definitions Dig

@0 nonempty : ∀ {@0 A} → NonEmpty A → NonEmpty (Generic.SeqElems A)
nonempty ne (x Generic.∷[]) refl = ne x refl
nonempty ne (Generic.cons (Generic.mkSeqElems h t bs≡)) refl =
  ne h (‼ ++-conicalˡ _ _ (sym bs≡))

@0 unambiguous : ∀ {@0 A} → Unambiguous A → NonEmpty A → NonNesting A → Unambiguous (Generic.SeqElems A)
unambiguous ua ne nn (x Generic.∷[]) (x₁ Generic.∷[]) =
  subst₀ (λ x' → x Generic.∷[] ≡ (x' Generic.∷[])) (ua x x₁) refl
unambiguous ua ne nn{xs} (x Generic.∷[]) (Generic.cons (Generic.mkSeqElems{bs}{bs₂ = bs₂} h t bs≡)) =
  ⊥-elim $ contradiction (nn (trans₀ (xs ++ [] ≡ xs ∋ (solve (++-monoid Dig))) bs≡) x h)
    λ where
      refl → ‼
        (case (++-cancelˡ xs (trans₀ (xs ++ [] ≡ xs ∋ solve (++-monoid Dig)) bs≡)) of λ eq →
          nonempty ne t (sym eq))
unambiguous ua ne nn {xs} (Generic.cons (Generic.mkSeqElems h t bs≡)) (x₁ Generic.∷[]) =
  ⊥-elim $ contradiction (nn (trans₀ (xs ++ [] ≡ xs ∋ solve (++-monoid Dig)) bs≡) x₁ h) λ where
    refl → ‼
      (case ++-cancelˡ xs (trans₀ (xs ++ [] ≡ xs ∋ solve (++-monoid Dig)) bs≡) of λ eq →
        nonempty ne t (sym eq))
unambiguous ua ne nn (Generic.cons (Generic.mkSeqElems{bs₁ = bs₁₁}{bs₁₂} h t bs≡)) (Generic.cons (Generic.mkSeqElems{bs₁ = bs₂₁}{bs₂₂} h₁ t₁ bs≡₁)) =
  ≡-elim (λ {bs₂₁} bs₁≡ → ∀ h₁ bs≡₁ → _ ≡ Generic.cons (Generic.mkSeqElems {bs₁ = bs₂₁} h₁ t₁ bs≡₁))
    (λ h₁ bs≡₁ →
      ≡-elim (λ {bs₂₂} bs₂≡ → ∀ t₁ bs≡₁ → _ ≡ Generic.cons (Generic.mkSeqElems{bs₂ = bs₂₂} h₁ t₁ bs≡₁))
        (λ t₁ bs≡₁ →
          subst₂ (λ x y → _ ≡ Generic.cons (Generic.mkSeqElems x y bs≡₁)) (ua h h₁) (unambiguous ua ne nn t t₁)
            (subst₀ (λ x → _ ≡ Generic.cons (Generic.mkSeqElems _ _ x)) (≡-unique bs≡ bs≡₁) refl))
        bs₂≡ t₁ bs≡₁)
    bs₁≡ h₁ bs≡₁
  where
  @0 bs≡' : bs₁₁ ++ bs₁₂ ≡ bs₂₁ ++ bs₂₂
  bs≡' = trans₀ (sym bs≡) bs≡₁

  @0 bs₁≡ : bs₁₁ ≡ bs₂₁
  bs₁≡ = nn bs≡' h h₁

  bs₂≡ : bs₁₂ ≡ bs₂₂
  bs₂≡ = Lemmas.++-cancel≡ˡ _ _ bs₁≡ bs≡'
