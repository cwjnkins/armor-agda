{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509
import      Aeres.Data.X509.Properties.TLV as TLVprops
open import Aeres.Prelude
open import Data.Nat.Properties
  hiding (_≟_)

module Aeres.Data.X509.Properties.MonthDayHourMinSecFields where

open Base256
open import Aeres.Grammar.Definitions Dig

@0 nonnesting : NonNesting Generic.MonthDayHourMinSecFields
nonnesting {xs₁ = xs₁} {xs₂ = xs₂} x (Generic.mkMDHMSFields mon monRange day dayRange hour hourRange min minRange sec secRange bs≡) (Generic.mkMDHMSFields mon₁ monRange₁ day₁ dayRange₁ hour₁ hourRange₁ min₁ minRange₁ sec₁ secRange₁ bs≡₁)
  with Lemmas.length-++-≡ xs₁ _ xs₂ _ x (trans₀ (cong length bs≡) (cong length (sym bs≡₁)))
... | fst , snd = fst

module MonthRange where
  unambiguous : ∀ {mo₁ mo₂} → (x y : Generic.MonthRange mo₁ mo₂) → x ≡ y
  unambiguous{mo₂ = mo₂} (inj₁ x) (inj₁ x₁) = cong inj₁ (×-unique ≡-unique (inRange-unique{l = '0'}{'9'}{mo₂}) x x₁)
  unambiguous (inj₁ x) (inj₂ y) = case trans₀ (sym (proj₁ y)) (proj₁ x) of λ ()
  unambiguous (inj₂ y) (inj₁ x) = case trans₀ (sym (proj₁ y)) (proj₁ x) of λ ()
  unambiguous{mo₂ = mo₂} (inj₂ y) (inj₂ y₁) = cong inj₂ (×-unique ≡-unique (inRange-unique{l = '0'}{'2'}{mo₂}) y y₁)

module DayRange where
  unambiguous : ∀ {d₁ d₂} → (x y : Generic.DayRange d₁ d₂) → x ≡ y
  unambiguous{d₁}{d₂} (inj₁ x) (inj₁ x₁) =
    cong inj₁ (×-unique (inRange-unique{l = '0'}{'2'}{d₁}) (inRange-unique{l = '0'}{'9'}{d₂}) x x₁)
  unambiguous (inj₁ x) (inj₂ y) = contradiction (proj₁ y) (<⇒≢ (s≤s (proj₂ (proj₁ x))))
  unambiguous (inj₂ y) (inj₁ x) = contradiction (proj₁ y) (<⇒≢ (s≤s (proj₂ (proj₁ x))))
  unambiguous{d₂ = d₂} (inj₂ y) (inj₂ y₁) =
    cong inj₂ (×-unique ≡-unique (inRange-unique{l = '0'}{'1'}{d₂}) y y₁)

module HourRange where
  unambiguous : ∀ {h₁ h₂} → (x y : Generic.HourRange h₁ h₂) → x ≡ y
  unambiguous{h₁}{h₂} (inj₁ x) (inj₁ x₁) =
    cong inj₁ (×-unique (inRange-unique{l = '0'}{'1'}{h₁}) (inRange-unique{l = '0'}{'9'}{h₂}) x x₁)
  unambiguous (inj₁ x) (inj₂ y) = contradiction (proj₁ y) (<⇒≢ (s≤s (proj₂ (proj₁ x))))
  unambiguous (inj₂ y) (inj₁ x) = contradiction (proj₁ y) (<⇒≢ (s≤s (proj₂ (proj₁ x))))
  unambiguous{h₂ = h₂} (inj₂ y) (inj₂ y₁) =
    cong inj₂ (×-unique ≡-unique (inRange-unique{l = '0'}{'3'}{h₂}) y y₁)

module MinuteRange where
  unambiguous : ∀ {mi₁ mi₂} → (x y : Generic.MinuteRange mi₁ mi₂) → x ≡ y
  unambiguous = ×-unique (inRange-unique{B = Dig}{l = '0'}{'5'}) (inRange-unique{B = Dig}{l = '0'}{'9'})

module SecRange where
  unambiguous = MinuteRange.unambiguous

@0 unambiguous : Unambiguous Generic.MonthDayHourMinSecFields
unambiguous (Generic.mkMDHMSFields{mo₁}{mo₂}{d₁}{d₂}{h₁}{h₂}{mi₁}{mi₂}{s₁}{s₂} mon monRange day dayRange hour hourRange min minRange sec secRange bs≡) (Generic.mkMDHMSFields{mo₁'}{mo₂'}{d₁'}{d₂'}{h₁'}{h₂'}{mi₁'}{mi₂'}{s₁'}{s₂'} mon₁ monRange₁ day₁ dayRange₁ hour₁ hourRange₁ min₁ minRange₁ sec₁ secRange₁ bs≡₁) =
  subst₂ (λ m1 m2 → ∀ mon₁ monRange₁ bs≡₁ → _ ≡ Generic.mkMDHMSFields{mo₁ = m1}{m2} mon₁ monRange₁ _ _ _ _ _ _ _ _ bs≡₁ )
    mo₁≡ mo₂≡
    (λ mon₁ monRange₁ bs≡₁ →
      subst₂ (λ d₁' d₂' → ∀ day₁ dayRange₁ bs≡₁ → _ ≡ Generic.mkMDHMSFields {d₁ = d₁'} {d₂'} _ _ day₁ dayRange₁ _ _ _ _ _ _ bs≡₁)
        d₁≡ d₂≡
        (λ day₁ dayRange₁ bs≡₁ →
          subst₂ (λ h₁' h₂' → ∀ hour₁ hourRange₁ bs≡₁ → _ ≡ Generic.mkMDHMSFields{h₁ = h₁'}{h₂'} _ _ _ _ hour₁ hourRange₁ _ _ _ _ bs≡₁)
            h₁≡ h₂≡
            (λ hour₁ hourRange₁ bs≡₁ →
              subst₂ (λ mi₁' mi₂' → ∀ min₁ minRange₁ bs≡₁ → _ ≡ Generic.mkMDHMSFields{mi₁ = mi₁'}{mi₂'} _ _ _ _ _ _ min₁ minRange₁ _ _ bs≡₁)
                mi₁≡ mi₂≡
                (λ min₁ minRange₁ bs≡₁ →
                  subst₂ (λ s₁' s₂' → ∀ sec₁ secRange₁ bs≡₁ → _ ≡ Generic.mkMDHMSFields{s₁ = s₁'}{s₂'} _ _ _ _ _ _ _ _ sec₁ secRange₁ bs≡₁) s₁≡ s₂≡
                    (λ sec₁ secRange₁ bs≡₁ →
                      subst₂ (λ mon₁ monRange₁ → _ ≡ Generic.mkMDHMSFields mon₁ monRange₁ _ _ _ _ _ _ _ _ _) (uniqueSingleton mon mon₁) (MonthRange.unambiguous monRange monRange₁)
                        (subst₂ (λ day₁ dayRange₁ → _ ≡ Generic.mkMDHMSFields _ _  day₁ dayRange₁ _ _ _ _ _ _ _) (uniqueSingleton day day₁) (DayRange.unambiguous dayRange dayRange₁)
                          (subst₂ (λ hour₁ hourRange₁ → _ ≡ Generic.mkMDHMSFields _ _ _ _ hour₁ hourRange₁ _ _ _ _ _) (uniqueSingleton hour hour₁) (HourRange.unambiguous hourRange hourRange₁)
                            (subst₂ (λ min₁ minRange₁ → _ ≡ Generic.mkMDHMSFields _ _ _ _ _ _ min₁ minRange₁ _ _ _) (uniqueSingleton min min₁) (MinuteRange.unambiguous minRange minRange₁)
                              (subst₂ (λ sec₁ secRange₁ → _ ≡ Generic.mkMDHMSFields _ _ _ _ _ _ _ _ sec₁ secRange₁ _) (uniqueSingleton sec sec₁) (SecRange.unambiguous secRange secRange₁)
                                (subst (λ bs≡₁ → _ ≡ Generic.mkMDHMSFields _ _ _ _ _ _ _ _ _ _ bs≡₁) (≡-unique bs≡ bs≡₁) refl))))))
                    sec₁ secRange₁ bs≡₁)
                min₁ minRange₁ bs≡₁)
            hour₁ hourRange₁ bs≡₁)
        day₁ dayRange₁ bs≡₁)
    mon₁ monRange₁ bs≡₁
  where
  @0 bs≡' : mo₁ ∷ mo₂ ∷ d₁ ∷ d₂ ∷ h₁ ∷ h₂ ∷ mi₁ ∷ mi₂ ∷ s₁ ∷ [ s₂ ] ≡ mo₁' ∷ mo₂' ∷ d₁' ∷ d₂' ∷ h₁' ∷ h₂' ∷ mi₁' ∷ mi₂' ∷ s₁' ∷ [ s₂' ]
  bs≡' = trans (sym bs≡) bs≡₁

  @0 mo₁≡ : mo₁ ≡ mo₁'
  mo₁≡ = ∷-injectiveˡ bs≡'

  @0 mo₂≡ : mo₂ ≡ mo₂'
  mo₂≡ = ∷-injectiveˡ (proj₂ (Lemmas.length-++-≡ [ _ ] _ [ _ ] _ bs≡' refl))

  @0 d₁≡ : d₁ ≡ d₁'
  d₁≡ = ∷-injectiveˡ (proj₂ (Lemmas.length-++-≡ (_ ∷ [ _ ]) _ (_ ∷ [ _ ]) _ bs≡' refl))

  @0 d₂≡ : d₂ ≡ d₂'
  d₂≡ = ∷-injectiveˡ (proj₂ (Lemmas.length-++-≡ (_ ∷ _ ∷ [ _ ]) _ (_ ∷ _ ∷ [ _ ]) _ bs≡' refl))

  @0 h₁≡ : h₁ ≡ h₁'
  h₁≡ = ∷-injectiveˡ (proj₂ (Lemmas.length-++-≡ (_ ∷ _ ∷ _ ∷ [ _ ]) _ (_ ∷ _ ∷ _ ∷ [ _ ]) _ bs≡' refl))

  @0 h₂≡ : h₂ ≡ h₂'
  h₂≡ = ∷-injectiveˡ (proj₂ (Lemmas.length-++-≡ (_ ∷ _ ∷ _ ∷ _ ∷ [ _ ]) _ (_ ∷ _ ∷ _ ∷ _ ∷ [ _ ]) _ bs≡' refl))

  @0 mi₁≡ : mi₁ ≡ mi₁'
  mi₁≡ = ∷-injectiveˡ (proj₂ (Lemmas.length-++-≡ (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ [ _ ]) _ (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ [ _ ]) _ bs≡' refl))

  @0 mi₂≡ : mi₂ ≡ mi₂'
  mi₂≡ = ∷-injectiveˡ (proj₂ (Lemmas.length-++-≡ (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ [ _ ]) _ (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ [ _ ]) _ bs≡' refl))

  @0 s₁≡ : s₁ ≡ s₁'
  s₁≡ = ∷-injectiveˡ (proj₂ (Lemmas.length-++-≡ (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ [ _ ]) _ (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ [ _ ]) _ bs≡' refl))

  @0 s₂≡ : s₂ ≡ s₂'
  s₂≡ = ∷-injectiveˡ (proj₂ (Lemmas.length-++-≡ (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ [ _ ]) _ (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ [ _ ]) _ bs≡' refl))


