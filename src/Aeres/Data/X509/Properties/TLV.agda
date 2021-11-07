{-# OPTIONS --subtyping #-}

open import Aeres.Prelude
open import Aeres.Binary
open import Aeres.Data.X509
import Aeres.Data.X509.Properties.Length as LengthProps
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Properties.TLV where

open Base256
open import Aeres.Grammar.Definitions Dig

postulate
  unambiguous : ∀ {t} {@0 A} → Unambiguous A → Unambiguous (Generic.TLV t A)

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
