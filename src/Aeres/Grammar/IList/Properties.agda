{-# OPTIONS --subtyping #-}

open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.TLV.Properties as TLV
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.IList.TCB
import      Aeres.Grammar.Option
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Seq
import      Aeres.Grammar.Sum
open import Aeres.Prelude
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Grammar.IList.Properties (Σ : Set) where

open Aeres.Grammar.Definitions Σ
open Aeres.Grammar.IList.TCB   Σ
open Aeres.Grammar.Option      Σ
open Aeres.Grammar.Properties  Σ
open Aeres.Grammar.Seq         Σ
open Aeres.Grammar.Sum         Σ

Rep : (List Σ → Set) → @0 List Σ → Set
Rep A = Sum (_≡ []) (&ₚ A (IList A))

equiv : ∀ {@0 A} → Equivalent (Rep A) (IList A)
proj₁ equiv (Sum.inj₁ refl) = nil
proj₁ equiv (Sum.inj₂ (mk&ₚ fstₚ₁ sndₚ₁ bs≡)) =
  consIList fstₚ₁ sndₚ₁ bs≡
proj₂ equiv nil = inj₁ refl
proj₂ equiv (consIList h t bs≡) =
  inj₂ (mk&ₚ h t bs≡)

iso : ∀ {@0 A} → Iso (Rep A) (IList A)
proj₁ iso = equiv
proj₁ (proj₂ iso) (Sum.inj₁ refl) = refl
proj₁ (proj₂ iso) (Sum.inj₂ (mk&ₚ fstₚ₁ sndₚ₁ bs≡)) = refl
proj₂ (proj₂ iso) nil = refl
proj₂ (proj₂ iso) (consIList h t bs≡) = refl

@0 unambiguous : ∀ {@0 A} → Unambiguous A → NonEmpty A → NoSubstrings A → Unambiguous (IList A)
unambiguous ua ne nn nil nil = refl
unambiguous ua ne nn{xs} nil (cons (mkIListCons{bs₁}{bs₂} h t bs≡)) =
  contradiction (++-conicalˡ _ _ (sym bs≡)) (ne h)
unambiguous ua ne nn {xs} (cons (mkIListCons h t bs≡)) nil =
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

lengthIList≡
  : ∀ {@0 A} → NonEmpty A → NoSubstrings A
    → ∀ {@0 xs} → (il₁ il₂ : IList A xs)
    → lengthIList il₁ ≡ lengthIList il₂
lengthIList≡ ne nn nil nil = refl
lengthIList≡ ne nn nil (cons (mkIListCons head tail bs≡)) =
  contradiction
    (++-conicalˡ _ _ (sym bs≡))
    (ne head)
lengthIList≡ ne nn (cons (mkIListCons head tail bs≡)) nil =
  contradiction
    (++-conicalˡ _ _ (sym bs≡))
    (ne head)
lengthIList≡{A} ne nn (cons (mkIListCons{bs₂ = bs₂} head tail refl)) (cons (mkIListCons head₁ tail₁ bs≡₁)) =
  cong suc
    (trans (lengthIList≡ ne nn {bs₂} tail tail')
      (‼ ≡-elim (λ {bs₁'} eq → lengthIList (subst₀ (IList A) eq tail₁) ≡ lengthIList tail₁) refl bs₂≡))
  where
  @0 bs₁≡ : _ ≡ _
  bs₁≡ = nn (sym bs≡₁) head₁ head

  @0 bs₂≡ : _ ≡ _
  bs₂≡ = Lemmas.++-cancel≡ˡ _ _ bs₁≡ (sym bs≡₁)

  tail' : IList A bs₂
  tail' = subst₀ (IList A) bs₂≡ tail₁

lengthIList≤
  : ∀ {@0 A} → NonEmpty A → NoSubstrings A
    → (@0 xs₁ xs₂ : List Σ) {@0 ys₁ ys₂ : List Σ}
    → xs₁ ++ ys₁ ≡ xs₂ ++ ys₂
    → @0 length xs₁ ≤ length xs₂
    → (v₁ : IList A xs₁) (v₂ : IList A xs₂)
    → lengthIList v₁ ≤ lengthIList v₂
lengthIList≤ ne nn .[] xs₂ ++≡ xs₁≤ nil v₂ = z≤n
lengthIList≤ ne nn .(bs₁ ++ bs₂) .[] ++≡ xs₁≤ (consIList{bs₁}{bs₂} head₁ tail₁ refl) nil =
  contradiction bs₁≡ (ne head₁)
  where
  @0 bs₁≡ : bs₁ ≡ []
  bs₁≡ = case (singleton bs₁ refl) of λ where
    (singleton [] refl) → refl
    (singleton (x ∷ x₁) refl) →
      contradiction xs₁≤ λ where ()
lengthIList≤ ne nn .(bs₁ ++ bs₂) xs₂{ys₁ = ys₁}{ys₂} ++≡ xs₁≤ (consIList{bs₁}{bs₂} head₁ tail₁ refl) (consIList{bs₁'}{bs₂'} head₂ tail₂ refl) =
  ≤.begin (1 + lengthIList tail₁
            ≤.≤⟨ +-monoʳ-≤ 1 (lengthIList≤ ne nn bs₂ bs₂'
                   (‼ Lemmas.++-cancel≡ˡ _ _ bs₁≡ ++≡')
                   bs₂≤ tail₁ tail₂) ⟩
          1 + lengthIList tail₂ ≤.∎)
  where
  open import Data.Nat.Properties
  open ≡-Reasoning
  module ≤ = ≤-Reasoning

  @0 ++≡' : bs₁ ++ bs₂ ++ ys₁ ≡ bs₁' ++ bs₂' ++ ys₂
  ++≡' =
    (begin bs₁ ++ bs₂ ++ ys₁ ≡⟨ solve (++-monoid Σ) ⟩
           (bs₁ ++ bs₂) ++ ys₁ ≡⟨ ++≡ ⟩
           (bs₁' ++ bs₂') ++ ys₂ ≡⟨ solve (++-monoid Σ) ⟩
           bs₁' ++ bs₂' ++ ys₂ ∎)

  @0 bs₁≡ : bs₁ ≡ bs₁'
  bs₁≡ = nn ++≡' head₁ head₂

  @0 bs₂≤ : length bs₂ ≤ length bs₂'
  bs₂≤ = +-cancelˡ-≤ (length bs₁)
           (≤.begin (length bs₁ + length bs₂ ≤.≡⟨ sym (length-++ bs₁) ⟩
                    length (bs₁ ++ bs₂) ≤.≤⟨ xs₁≤ ⟩
                    length (bs₁' ++ bs₂') ≤.≡⟨ length-++ bs₁' ⟩
                    length bs₁' + length bs₂' ≤.≡⟨ cong ((_+ _) ∘ length) (sym bs₁≡) ⟩
                    length bs₁ + length bs₂' ≤.∎))

private
  eqIListWF
    : ∀ {@0 A : @0 List Σ → Set} ⦃ _ : Eq (Exists─ (List Σ) A) ⦄
      → {@0 xs ys : List Σ} (a₁ : IList A xs) (a₂ : IList A ys)
      → @0 Acc _<_ (lengthIList a₁)
      → Dec (_≡_{A = Exists─ (List Σ) (IList A)} (─ xs , a₁) (─ ys , a₂))
  eqIListWF nil nil (WellFounded.acc rs) = yes refl
  eqIListWF nil (consIList h t bs≡) (WellFounded.acc rs) = no λ ()
  eqIListWF (consIList h t bs≡) nil (WellFounded.acc rs) = no λ ()
  eqIListWF (consIList h t refl) (consIList h₁ t₁ refl) (WellFounded.acc rs)
    = case (─ _ ,e h) ≟ (─ _ ,e h₁) ret (const _) of λ where
        (no ¬p) → no λ where refl → contradiction refl ¬p
        (yes refl) →
          case eqIListWF t t₁ (rs _ ≤-refl) ret (const _) of λ where
            (no ¬p) → no λ where refl → contradiction refl ¬p
            (yes refl) → yes refl
    where
    open import Data.Nat.Properties hiding (_≟_)

IListEq : ∀ {@0 A : @0 List Σ → Set} ⦃ _ : Eq (Exists─ (List Σ) A) ⦄
          → Eq (Exists─ (List Σ) (IList A))
Eq._≟_ IListEq (─ xs₁ , a₁) (─ xs₂ , a₂) = eqIListWF a₁ a₂ (<-wellFounded _)
  where open import Data.Nat.Induction

IListEq≋ : ∀ {@0 A : @0 List Σ → Set} ⦃ _ : Eq≋ A ⦄ → Eq≋ (IList A)
IListEq≋ = Eq⇒Eq≋ (IListEq ⦃ Eq≋⇒Eq it ⦄)

@0 nonmalleable : ∀ {A : @0 List Σ → Set} {R : Raw A} → NonEmpty A → NoSubstrings A → NonMalleable R → NonMalleable (RawIList R)
nonmalleable {A} {R} ne nn N a₁ a₂ eq = noma a₁ a₂ eq (Nat.<-wellFounded _)
  where
  import Data.Nat.Induction as Nat

  noma : ∀ {@0 bs₁ bs₂} → (a₁ : IList A bs₁) (a₂ : IList A bs₂)
         → Raw.to (RawIList R) a₁ ≡ Raw.to (RawIList R) a₂
         → @0 Acc _<_ (lengthIList a₂)
         → _≡_{A = Exists─ (List Σ) (IList A)} (─ bs₁ , a₁) (─ bs₂ , a₂)
  noma nil nil eq (Nat.acc rs) = refl
  noma (consIList head₁ tail₁ refl) (consIList head₂ tail₂ refl) eq (Nat.acc rs) =
    case N head₁ head₂ (∷-injectiveˡ eq) ret (const _) of λ where
      refl → case ‼ noma tail₁ tail₂ (∷-injectiveʳ eq) (rs _ ≤-refl) ret (const _) of λ where
        refl → refl
