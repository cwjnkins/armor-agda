{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509
import      Aeres.Data.X509.Properties.TLV as TLVprops
import      Aeres.Data.X509.Properties.MonthDayHourMinSecFields as MDHMSProps
open import Aeres.Prelude
open import Data.Nat.Properties
  hiding (_≟_)

module Aeres.Data.X509.Properties.Time where

open Base256
open import Aeres.Grammar.Definitions Dig

nonempty : NonEmpty Generic.Time
nonempty (Generic.utctm ()) refl
nonempty (Generic.gentm ()) refl

module UTC where
  @0 nonnesting : NonNesting Generic.UtcTimeFields
  nonnesting {xs₁ = xs₁} {xs₂ = xs₂} x (Generic.mkUtcTimeFields year yearRange mmddhhmmss term bs≡) (Generic.mkUtcTimeFields year₁ yearRange₁ mmddhhmmss₁ term₁ bs≡₁)
    with Lemmas.length-++-≡ xs₁ _ xs₂ _ x (trans₀ (cong length bs≡) (cong length (sym bs≡₁)))
  ... | fst , snd = fst

  postulate
    @0 unambiguous : Unambiguous Generic.UtcTimeFields

module GenTime where
  @0 nonnesting : NonNesting Generic.GenTimeFields
  nonnesting {xs₁ = xs₁} {xs₂ = xs₂} x (Generic.mkGenTimeFields year yearRange (Generic.mkMDHMSFields mon monRange day dayRange hour hourRange min minRange sec secRange refl) z≡ bs≡) (Generic.mkGenTimeFields year₁ yearRange₁ (Generic.mkMDHMSFields mon₁ monRange₁ day₁ dayRange₁ hour₁ hourRange₁ min₁ minRange₁ sec₁ secRange₁ refl) z≡₁ bs≡₁)
    with Lemmas.length-++-≡ xs₁ _ xs₂ _ x (trans₀ (cong length bs≡) (cong length (sym bs≡₁)))
  ... | fst , snd = fst

  @0 unambiguous : Unambiguous Generic.GenTimeFields
  unambiguous (Generic.mkGenTimeFields{y1 = y1}{y2}{y3}{y4}{z}{mdhms} year yearRange mmddhhmmss refl bs≡) (Generic.mkGenTimeFields{y1 = y1'}{y2'}{y3'}{y4'}{z'}{mdhms'} year₁ yearRange₁ mmddhhmmss₁ refl bs≡₁) =
    subst₂
      (λ y1“ y2“ → ∀ (year₁ : Singleton (asciiNum (y1“ ∷ y2“ ∷ y3' ∷ [ y4' ]))) (yearRange₁ : All (InRange '0' '9') (y1“ ∷ y2“ ∷ y3' ∷ [ y4' ])) bs≡₁
        → _ ≡ Generic.mkGenTimeFields year₁ yearRange₁ mmddhhmmss₁ refl bs≡₁)
      y1≡ y2≡
      (λ year₁ yearRange₁ bs≡₁ →
        subst₂ (λ y3“ y4“ → ∀ (year₁ : Singleton (asciiNum (y1 ∷ y2 ∷ y3“ ∷ [ y4“ ]))) (yearRange₁ : All (InRange '0' '9') (y1 ∷ y2 ∷ y3“ ∷ [ y4“ ])) bs≡₁ →
          _ ≡ Generic.mkGenTimeFields year₁ yearRange₁ mmddhhmmss₁ refl bs≡₁)
          y3≡ y4≡
          (λ year₁ yearRange₁ bs≡₁ →
            subst (λ mdhms“ → ∀ (mmddhhmmss₁ : Generic.MonthDayHourMinSecFields mdhms“) bs≡₁ → _ ≡ Generic.mkGenTimeFields year₁ yearRange₁ mmddhhmmss₁ refl bs≡₁) mdhms≡
              (λ mmddhhmmss₁ bs≡₁ →
                subst₂ (λ year₁ yearRange₁ → _ ≡ Generic.mkGenTimeFields year₁ yearRange₁ mmddhhmmss₁ refl bs≡₁)
                  (uniqueSingleton year _) (All.irrelevant (×-unique ≤-irrelevant ≤-irrelevant) yearRange yearRange₁)
                    (subst₂
                      (λ mmddhhmmss₁ bs≡₁ → _ ≡ Generic.mkGenTimeFields _ _ mmddhhmmss₁ _ bs≡₁)
                      (MDHMSProps.unambiguous mmddhhmmss _) (≡-unique bs≡ bs≡₁) refl))
              mmddhhmmss₁ bs≡₁)
          year₁ yearRange₁ bs≡₁)
      year₁ yearRange₁ bs≡₁
    where
    @0 bs≡' : y1 ∷ y2 ∷ y3 ∷ y4 ∷ mdhms ∷ʳ # 'Z' ≡ y1' ∷ y2' ∷ y3' ∷ y4' ∷ mdhms' ∷ʳ # 'Z'
    bs≡' = trans₀ (sym bs≡) bs≡₁

    @0 y1≡ : y1 ≡ y1'
    y1≡ = ∷-injectiveˡ bs≡'

    @0 y2≡ : y2 ≡ y2'
    y2≡ = ∷-injectiveˡ (proj₂ (Lemmas.length-++-≡ [ _ ] _ [ _ ] _ bs≡' refl))

    @0 y3≡ : y3 ≡ y3'
    y3≡ = ∷-injectiveˡ (proj₂ (Lemmas.length-++-≡ (_ ∷ [ _ ]) _ (_ ∷ [ _ ]) _ bs≡' refl))

    @0 y4≡ : y4 ≡ y4'
    y4≡ = ∷-injectiveˡ (proj₂ (Lemmas.length-++-≡ (_ ∷ _ ∷ [ _ ]) _ (_ ∷ _ ∷ [ _ ]) _ bs≡' refl))

    @0 mdhms≡ : mdhms ≡ mdhms'
    mdhms≡ = ++-cancelʳ _ _ (proj₂ (Lemmas.length-++-≡ (_ ∷ _ ∷ _ ∷ [ _ ]) _ (_ ∷ _ ∷ _ ∷ [ _ ]) _ bs≡' refl))

@0 nonnesting : NonNesting Generic.Time
nonnesting x (Generic.utctm x₁) (Generic.utctm x₂) = ‼ TLVprops.nonnesting x x₁ x₂
nonnesting x (Generic.utctm x₁) (Generic.gentm x₂) = ⊥-elim (TLVprops.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (Generic.gentm x₁) (Generic.utctm x₂) = ⊥-elim (TLVprops.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (Generic.gentm x₁) (Generic.gentm x₂) = ‼ TLVprops.nonnesting x x₁ x₂

@0 unambiguous : Unambiguous Generic.Time
unambiguous (Generic.utctm x) (Generic.utctm x₁) = cong Generic.utctm $ TLVprops.unambiguous UTC.unambiguous x x₁
unambiguous (Generic.utctm x) (Generic.gentm x₁) = ⊥-elim (TLVprops.noconfusion (λ ()) (cong (_++ []) refl) x x₁)
unambiguous (Generic.gentm x) (Generic.utctm x₁) = ⊥-elim (TLVprops.noconfusion (λ ()) (cong (_++ []) refl) x x₁)
unambiguous (Generic.gentm x) (Generic.gentm x₁) = cong Generic.gentm $ TLVprops.unambiguous GenTime.unambiguous x x₁
