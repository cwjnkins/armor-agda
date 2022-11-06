{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.OID.TCB
open import Aeres.Data.X690-DER.SequenceOf
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.IList
open import Aeres.Prelude
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X690-DER.OID.Properties where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.IList       UInt8

module Sub where
  nonempty : NonEmpty OIDSub
  nonempty (mkOIDSub [] lₚ≥128 lₑ lₑ<128 leastDigs ()) refl
  nonempty (mkOIDSub (x ∷ lₚ) lₚ≥128 lₑ lₑ<128 leastDigs ()) refl

  @0 unambiguous : Unambiguous OIDSub
  unambiguous (mkOIDSub lₚ lₚ≥128 lₑ lₑ<128 leastDigs refl) (mkOIDSub lₚ₁ lₚ≥129 lₑ₁ lₑ<129 leastDigs₁ bs≡₁) =
    ≡-elim (λ {lₚ₁} lₚ≡ → ∀ lₚ₁≥128 leastDigs₁ bs≡₁ → mkOIDSub lₚ lₚ≥128 lₑ lₑ<128 leastDigs refl ≡ mkOIDSub lₚ₁ lₚ₁≥128 lₑ₁ lₑ<129 leastDigs₁ bs≡₁)
      (λ lₚ₁≥128 leastDigs₁ bs≡₁' →
        ≡-elim (λ {lₑ₁} lₑ≡ → ∀ lₑ₁<128 bs≡₁ → mkOIDSub lₚ lₚ≥128 lₑ lₑ<128 leastDigs refl ≡ mkOIDSub lₚ lₚ₁≥128 lₑ₁ lₑ₁<128 leastDigs₁ bs≡₁)
          (λ where
            lₑ₁<128 refl → ‼
              subst₂ (λ x y → mkOIDSub lₚ lₚ≥128 lₑ lₑ<128 leastDigs refl ≡ mkOIDSub lₚ x lₑ y leastDigs₁ refl)
                (All.irrelevant ≤-irrelevant lₚ≥128 _) (≤-irrelevant lₑ<128 _)
                (subst₀ (λ x → mkOIDSub lₚ lₚ≥128 lₑ lₑ<128 leastDigs refl ≡ mkOIDSub _ lₚ≥128 _ lₑ<128 x refl) (leastBytesUnique{bs = lₚ} leastDigs leastDigs₁)
                  refl))
          lₑ≡ lₑ<129 bs≡₁')
      lₚ≡ lₚ≥129 leastDigs₁ bs≡₁
    where
    @0 lₚ≡ : lₚ ≡ lₚ₁
    lₚ≡ = ∷ʳ-injectiveˡ _ _ bs≡₁
  
    @0 lₑ≡ : lₑ ≡ lₑ₁
    lₑ≡ = ∷ʳ-injectiveʳ _ _ bs≡₁

  instance
    OIDSub≋ : Eq≋ OIDSub
    Eq≋._≋?_ OIDSub≋ {bs} {bs₁} a₁@(mkOIDSub lₚ lₚ≥128 lₑ lₑ<128 leastDigs bs≡) a₂@(mkOIDSub lₚ₁ lₚ≥129 lₑ₁ lₑ<129 leastDigs₁ bs≡₁)
      with lₚ ∷ʳ lₑ ≟ lₚ₁ ∷ʳ lₑ₁
    ... | yes bs≡bs₁ =
      yes (mk≋ bs≡bs₁' (unambiguous (subst OIDSub bs≡bs₁' a₁) a₂))
      where
      @0 bs≡bs₁' : bs ≡ bs₁
      bs≡bs₁' = trans bs≡ (trans bs≡bs₁ (sym bs≡₁))
    ... | no ¬bs≡bs₁ = no λ where
      (mk≋ bs≡bs₁ a≡) → contradiction (trans (sym bs≡) (trans bs≡bs₁ bs≡₁)) ¬bs≡bs₁

  @0 nonnesting : NonNesting OIDSub
  nonnesting {ys₁ = ys₁} {ys₂ = ys₂} ++≡ (mkOIDSub lₚ₁ lₚ₁≥128 lₑ₁ lₑ₁<128 leastDigs₁ refl) (mkOIDSub lₚ₂ lₚ₂≥128 lₑ₂ lₑ₂<128 leastDigs₂ refl)
    with Lemmas.++-≡-⊆ (lₚ₁ ∷ʳ lₑ₁) _ (lₚ₂ ∷ʳ lₑ₂) _ ++≡
  ... | 0 , inj₁ xs₁⊆xs₂ = trans₀ (lₚ₁ ++ lₑ₁ ∷ [] ≡ (lₚ₁ ++ lₑ₁ ∷ []) ++ [] ∋ solve (++-monoid UInt8)) xs₁⊆xs₂
  ... | 0 , inj₂ xs₂⊆xs₁ = trans₀ xs₂⊆xs₁ ((lₚ₂ ++ lₑ₂ ∷ []) ++ [] ≡ lₚ₂ ++ lₑ₂ ∷ [] ∋ solve (++-monoid UInt8))
  ... | suc n , inj₁ xs₁⊆xs₂
    with ys₁
  ... | [] = trans₀ (lₚ₁ ++ lₑ₁ ∷ [] ≡ (lₚ₁ ++ lₑ₁ ∷ []) ++ [] ∋ solve (++-monoid UInt8)) xs₁⊆xs₂
  ... | y₁ ∷ ys₁ =
    contradiction
      (lem xs₁⊆xs₂ lₚ₂≥128)
      (<⇒≱ lₑ₁<128)
    where
    -- TODO: refactor this.
    -- This is a general result about anything which is the result of a terminated "TakeWhile"
    lem : ∀ {ws w x xs ys y} → ws ∷ʳ w ++ x ∷ xs ≡ ys ∷ʳ y → All ((128 ≤_) ∘ toℕ) ys → 128 ≤ toℕ w
    lem {[]} {xs = xs} {y' ∷ ys} ++≡ (py' All.∷ ys≤128) rewrite ∷-injectiveˡ ++≡ = py'
    lem {x ∷ ws}{w} {xs = xs} {[]} ++≡ ys≤128 =
      contradiction
        (++-conicalˡ _ _ (∷-injectiveʳ ++≡))
        (Lemmas.∷ʳ⇒≢[]{xs = ws}{w})
    lem {x ∷ ws} {xs = xs} {x₁ ∷ ys} ++≡ (_ All.∷ ys≤128) = lem (∷-injectiveʳ ++≡) ys≤128
  nonnesting {ys₁ = ys₁} {ys₂ = ys₂} ++≡ (mkOIDSub lₚ₁ lₚ₁≥128 lₑ₁ lₑ₁<128 leastUInt8s₁ refl) (mkOIDSub lₚ₂ lₚ₂≥128 lₑ₂ lₑ₂<128 leastUInt8s₂ refl) | suc n , inj₂ xs₂⊆xs₁
    with ys₂
  ... | [] = trans₀ xs₂⊆xs₁ ((lₚ₂ ++ lₑ₂ ∷ []) ++ [] ≡ lₚ₂ ++ lₑ₂ ∷ [] ∋ solve (++-monoid UInt8))
  ... | y₂ ∷ ys₂ =
    contradiction
      (lem (sym xs₂⊆xs₁) lₚ₁≥128)
      (<⇒≱ lₑ₂<128)
    where
    lem : ∀ {ws w x xs ys y} → ws ∷ʳ w ++ x ∷ xs ≡ ys ∷ʳ y → All ((128 ≤_) ∘ toℕ) ys → 128 ≤ toℕ w
    lem {[]} {xs = xs} {y' ∷ ys} ++≡ (py' All.∷ ys≤128) rewrite ∷-injectiveˡ ++≡ = py'
    lem {x ∷ ws}{w} {xs = xs} {[]} ++≡ ys≤128 =
      contradiction
        (++-conicalˡ _ _ (∷-injectiveʳ ++≡))
        (Lemmas.∷ʳ⇒≢[]{xs = ws}{w})
    lem {x ∷ ws} {xs = xs} {x₁ ∷ ys} ++≡ (_ All.∷ ys≤128) = lem (∷-injectiveʳ ++≡) ys≤128

module OID where
  @0 unambiguous : Unambiguous OID
  unambiguous =
    TLV.unambiguous
      (SequenceOf.Bounded.unambiguous
        Sub.unambiguous Sub.nonempty Sub.nonnesting)

module OIDSeq where
  @0 unambiguous : Unambiguous (SequenceOf OID)
  unambiguous = SequenceOf.unambiguous OID.unambiguous TLV.nonempty TLV.nonnesting

open OID public

instance
  OIDEq : Eq (Exists─ (List UInt8) OIDValue)
  (OIDEq Eq.≟ (─ x , snd)) (─ x₁ , snd₁)
    with snd ≋? snd₁
  ... | no ¬p = no λ where
    refl → contradiction ≋-refl ¬p
  ... | yes ≋-refl = yes refl

  OIDEq≋ : Eq≋ OIDValue
  OIDEq≋ = Eq⇒Eq≋ it
