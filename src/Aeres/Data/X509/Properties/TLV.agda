{-# OPTIONS --subtyping #-}

open import Aeres.Prelude
open import Aeres.Binary
open import Aeres.Data.X509
import      Aeres.Grammar.Definitions
import Aeres.Data.X509.Properties.Length as LengthProps
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Properties.TLV where

open Base256
open Aeres.Grammar.Definitions Dig

nonempty : ∀ {t} {@0 A} → NonEmpty (Generic.TLV t A)
nonempty (Generic.mkTLV len val len≡ ()) refl

@0 nonnesting : ∀ {t} {@0 A} → NonNesting (Generic.TLV t A)
nonnesting{t}{xs₁ = xs₁}{ys₁}{xs₂}{ys₂} xs₁++ys₁≡xs₂++ys₂ (Generic.mkTLV{l}{v} len val len≡ bs≡) (Generic.mkTLV{l₁}{v₁} len₁ val₁ len≡₁ bs≡₁) =
  ‼ (begin xs₁ ≡⟨ bs≡ ⟩
           t ∷ l ++ v ≡⟨ cong (t ∷_) (cong (_++ v) l≡) ⟩
           t ∷ l₁ ++ v ≡⟨ cong (t ∷_) (cong (l₁ ++_) v≡) ⟩
           t ∷ l₁ ++ v₁ ≡⟨ sym bs≡₁ ⟩
           xs₂ ∎)
  where
  open ≡-Reasoning
  @0 l++≡ : l ++ v ++ ys₁ ≡ l₁ ++ v₁ ++ ys₂
  l++≡ = ∷-injectiveʳ (begin (t ∷ l ++ v ++ ys₁     ≡⟨ cong (t ∷_) (solve (++-monoid Dig)) ⟩
                              t ∷ (l ++ v) ++ ys₁   ≡⟨ cong (_++ ys₁) (sym bs≡) ⟩
                              xs₁ ++ ys₁            ≡⟨ xs₁++ys₁≡xs₂++ys₂ ⟩
                              xs₂ ++ ys₂            ≡⟨ cong (_++ ys₂) bs≡₁ ⟩
                              t ∷ (l₁ ++ v₁) ++ ys₂ ≡⟨ cong (t ∷_) (solve (++-monoid Dig)) ⟩
                              t ∷ l₁ ++ v₁ ++ ys₂   ∎))

  @0 l≡ : l ≡ l₁
  l≡ = LengthProps.nonnesting l++≡ len len₁

  @0 v≡ : v ≡ v₁
  v≡ = proj₁ $ Lemmas.length-++-≡ _ _ _ _
                 (++-cancelˡ l (trans l++≡ (cong (_++ v₁ ++ ys₂) (sym l≡))))
                 (begin length v       ≡⟨ sym len≡ ⟩
                        getLength len  ≡⟨ LengthProps.unambiguous-getLength l≡ len len₁ ⟩
                        getLength len₁ ≡⟨ len≡₁ ⟩
                        length v₁      ∎)

@0 noconfusion : ∀ {@0 A₁ A₂} {t₁ t₂} → t₁ ≢ t₂ → NoConfusion (Generic.TLV t₁ A₁) (Generic.TLV t₂ A₂)
noconfusion t₁≢t₂{xs₁}{ys₁}{xs₂}{ys₂} xs₁++ys₁≡xs₂++ys₂ (Generic.mkTLV len val len≡ bs≡) (Generic.mkTLV len₁ val₁ len≡₁ bs≡₁) =
 contradiction (∷-injectiveˡ (trans (cong (_++ ys₁) (sym bs≡)) (trans xs₁++ys₁≡xs₂++ys₂ (cong (_++ ys₂) bs≡₁)))) t₁≢t₂

module TLV where
  @0 unambiguous : ∀ {t} {@0 A} → Unambiguous A → Unambiguous (Generic.TLV t A)
  unambiguous{t}{A} ua (Generic.mkTLV{l = l₁}{v₁} len₁ val₁ len≡₁ bs≡₁) (Generic.mkTLV{l = l₂}{v₂} len₂ val₂ len≡₂ bs≡₂) =
    subst₀ (λ l₂ → ∀ (len₂ : Length l₂) len≡₂ bs≡₂ → Generic.mkTLV len₁ val₁ len≡₁ bs≡₁ ≡ Generic.mkTLV {l = l₂} len₂ val₂ len≡₂ bs≡₂ ) l≡
      (λ len₂ len≡₂ bs≡₂' →
        subst₀ (λ v₂ → ∀ (val₂ : A v₂) len≡₂ bs≡₂ → Generic.mkTLV len₁ val₁ len≡₁ bs≡₁ ≡ Generic.mkTLV len₂ val₂ len≡₂ bs≡₂) v≡
          (λ val₂ len≡₂ bs≡₂' →
            subst₂ (λ len₂ val₂ → ∀ len≡₂ → Generic.mkTLV len₁ val₁ len≡₁ bs≡₁ ≡ Generic.mkTLV len₂ val₂ len≡₂ bs≡₂')
              (LengthProps.unambiguous len₁ len₂) (ua val₁ val₂)
              (λ len≡₂ →
                subst₂ (λ x y → _ ≡ Generic.mkTLV len₁ val₁ x y) (≡-unique len≡₁ len≡₂) (≡-unique bs≡₁ bs≡₂')
                  refl)
              len≡₂ )
          val₂ len≡₂ bs≡₂')
      len₂ len≡₂ bs≡₂
    where
    @0 bs≡' : l₁ ++ v₁ ≡ l₂ ++ v₂
    bs≡' = ∷-injectiveʳ (trans₀ (sym bs≡₁) bs≡₂)
  
    @0 l≡ : l₁ ≡ l₂
    l≡ = LengthProps.nonnesting bs≡' len₁ len₂
  
    @0 v≡ : v₁ ≡ v₂
    v≡ = Lemmas.++-cancel≡ˡ _ _ l≡ bs≡'

module NonEmptyVal where
  @0 unambiguous : ∀ {t} {@0 A} → Unambiguous A → Unambiguous (Σₚ (Generic.TLV t A) Generic.NonEmptyVal)
  unambiguous ua = unambiguousΣₚ (TLV.unambiguous ua) λ tlv → ≤-irrelevant

open TLV public

instance
  EqTLV : ∀ {A : @0 List Dig → Set} ⦃ _ : Eq≋ A ⦄ → ∀ {t} → Eq≋ (Generic.TLV t A)
  Eq≋._≋?_ (EqTLV{t = t}) {bs₁} {bs₂} t₁ t₂
    with Generic.TLV.len t₁ ≋? Generic.TLV.len t₂
    |    Generic.TLV.val t₁ ≋? Generic.TLV.val t₂
  ... | no ¬len₁≋len₂ | _ = no λ where
    (mk≋ refl refl) → contradiction ≋-refl ¬len₁≋len₂
  ... | yes ≋-refl | no ¬v₁≋v₂ = no λ where
    ≋-refl → contradiction ≋-refl ¬v₁≋v₂
  ... | yes ≋-refl | yes ≋-refl
    with ‼ ≡-unique (Generic.TLV.len≡ t₁) (Generic.TLV.len≡ t₂)
  ... | refl
    with ‼ bs₁≡bs₂
    where
    @0 bs₁≡bs₂ : bs₁ ≡ bs₂
    bs₁≡bs₂ = trans (Generic.TLV.bs≡ t₁) (sym (Generic.TLV.bs≡ t₂))
  ... | refl
    with ‼ ≡-unique (Generic.TLV.bs≡ t₁) (Generic.TLV.bs≡ t₂)
  ... | refl = yes ≋-refl

@0 getLengthLen≡ : ∀ {t} {A : List Dig → Set} {@0 xs₁ ys₁ xs₂ ys₂} → xs₁ ++ ys₁ ≡ xs₂ ++ ys₂
                   → (v₁ : Generic.TLV t A xs₁) (v₂ : Generic.TLV t A xs₂) → getLength (Generic.TLV.len v₁) ≡ getLength (Generic.TLV.len v₂)
getLengthLen≡{t}{xs₁ = xs₁}{ys₁}{xs₂}{ys₂} ++≡ v₁ v₂
  with LengthProps.nonnesting (∷-injectiveʳ bs≡') (Generic.TLV.len v₁) (Generic.TLV.len v₂)
  where
  open ≡-Reasoning
  bs≡' : t ∷ Generic.TLV.l v₁ ++ Generic.TLV.v v₁ ++ ys₁ ≡ t ∷ Generic.TLV.l v₂ ++ Generic.TLV.v v₂ ++ ys₂
  bs≡' = begin
    t ∷ Generic.TLV.l v₁ ++ Generic.TLV.v v₁ ++ ys₁   ≡⟨ cong (t ∷_) (sym $ ++-assoc (Generic.TLV.l v₁) _ _) ⟩
    (t ∷ Generic.TLV.l v₁ ++ Generic.TLV.v v₁) ++ ys₁ ≡⟨ cong (_++ ys₁) (sym $ Generic.TLV.bs≡ v₁) ⟩
    xs₁ ++ ys₁                                        ≡⟨ ++≡ ⟩
    xs₂ ++ ys₂                                        ≡⟨ cong (_++ ys₂) (Generic.TLV.bs≡ v₂) ⟩
    (t ∷ Generic.TLV.l v₂ ++ Generic.TLV.v v₂) ++ ys₂ ≡⟨ cong (t ∷_) (++-assoc (Generic.TLV.l v₂) _ _) ⟩
    t ∷ Generic.TLV.l v₂ ++ Generic.TLV.v v₂ ++ ys₂   ∎
... | refl = cong getLength (LengthProps.unambiguous (Generic.TLV.len v₁) (Generic.TLV.len v₂))

