{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.Boool
open import Aeres.Data.X690-DER.TLV
open import Aeres.Data.X690-DER.Time.TCB
  hiding (module MonthDayHourMinSecFields)
import      Aeres.Grammar.Definitions
open import Aeres.Prelude
open import Data.Nat.Properties
  hiding (_≟_)

module Aeres.Data.X690-DER.Time.Properties where

open Base256
open Aeres.Grammar.Definitions UInt8

nonempty : NonEmpty Time
nonempty (utctm ()) refl
nonempty (gentm ()) refl

module MonthRange where
  unambiguous : ∀ {mo₁ mo₂} → (x y : MonthRange mo₁ mo₂) → x ≡ y
  unambiguous{mo₂ = mo₂} (inj₁ x) (inj₁ x₁) = cong inj₁ (×-unique ≡-unique (inRange-unique{l = '0'}{'9'}{mo₂}) x x₁)
  unambiguous (inj₁ x) (inj₂ y) = case trans₀ (sym (proj₁ y)) (proj₁ x) of λ ()
  unambiguous (inj₂ y) (inj₁ x) = case trans₀ (sym (proj₁ y)) (proj₁ x) of λ ()
  unambiguous{mo₂ = mo₂} (inj₂ y) (inj₂ y₁) = cong inj₂ (×-unique ≡-unique (inRange-unique{l = '0'}{'2'}{mo₂}) y y₁)

  monthRange? : ∀ mo₁ mo₂ → Dec (MonthRange mo₁ mo₂)
  monthRange? mo₁ mo₂ = mo₁ ≟ # '0' ×-dec inRange? '0' '9' mo₂ ⊎-dec mo₁ ≟ # '1' ×-dec inRange? '0' '2' mo₂

  monthRange⇒asciinum : ∀ {mo₁ mo₂} → MonthRange mo₁ mo₂ → All (InRange '0' '9') (mo₁ ∷ [ mo₂ ])
  monthRange⇒asciinum {mo₁} {mo₂} (inj₁ (refl , snd)) =
    (≤-refl , toWitness{Q = _ ≤? _} tt) ∷ _∷_{x = mo₂} snd []
  monthRange⇒asciinum {.(# '1')} {mo₂} (inj₂ (refl , snd)) =
      (toWitness{Q = inRange? '0' '9' '1'} tt)
    ∷ inRange-relax{B = UInt8}{l = '0'}{'0'}{'2'}{'9'} snd ≤-refl (toWitness{Q = toℕ '2' ≤? _} tt) ∷ []

module DayRange where
  unambiguous : ∀ {d₁ d₂} → (x y : DayRange d₁ d₂) → x ≡ y
  unambiguous{d₁}{d₂} (inj₁ x) (inj₁ x₁) =
    cong inj₁ (×-unique (inRange-unique{l = '0'}{'2'}{d₁}) (inRange-unique{l = '0'}{'9'}{d₂}) x x₁)
  unambiguous (inj₁ x) (inj₂ y) = contradiction (proj₁ y) (<⇒≢ (s≤s (proj₂ (proj₁ x))))
  unambiguous (inj₂ y) (inj₁ x) = contradiction (proj₁ y) (<⇒≢ (s≤s (proj₂ (proj₁ x))))
  unambiguous{d₂ = d₂} (inj₂ y) (inj₂ y₁) =
    cong inj₂ (×-unique ≡-unique (inRange-unique{l = '0'}{'1'}{d₂}) y y₁)

  dayRange? : ∀ d₁ d₂ → Dec (DayRange d₁ d₂)
  dayRange? d₁ d₂ = inRange? '0' '2' d₁ ×-dec inRange? '0' '9' d₂ ⊎-dec toℕ d₁ ≟ toℕ '3' ×-dec inRange? '0' '1' d₂

  asciinum : ∀ {d₁ d₂} → DayRange d₁ d₂ → All (InRange '0' '9') (d₁ ∷ [ d₂ ])
  asciinum (inj₁ x) =   inRange-relax{B = UInt8}{l = '0'}{'0'}{'2'}{'9'} (proj₁ x) ≤-refl (toWitness{Q = _ ≤? _} tt)
                      ∷ proj₂ x
                      ∷ []
  asciinum (inj₂ (x , y)) =
      (≤-trans (toWitness{Q = _ ≤? _} tt) (Lemmas.≡⇒≤ (sym x))
      , ≤-trans (Lemmas.≡⇒≤ x) (toWitness{Q = _ ≤? _} tt))
    ∷ inRange-relax {B = UInt8} {l = '0'} {'0'} {'1'} {'9'} y ≤-refl (toWitness{Q = _ ≤? _} tt)
    ∷ []

module HourRange where
  unambiguous : ∀ {h₁ h₂} → (x y : HourRange h₁ h₂) → x ≡ y
  unambiguous{h₁}{h₂} (inj₁ x) (inj₁ x₁) =
    cong inj₁ (×-unique (inRange-unique{l = '0'}{'1'}{h₁}) (inRange-unique{l = '0'}{'9'}{h₂}) x x₁)
  unambiguous (inj₁ x) (inj₂ y) = contradiction (proj₁ y) (<⇒≢ (s≤s (proj₂ (proj₁ x))))
  unambiguous (inj₂ y) (inj₁ x) = contradiction (proj₁ y) (<⇒≢ (s≤s (proj₂ (proj₁ x))))
  unambiguous{h₂ = h₂} (inj₂ y) (inj₂ y₁) =
    cong inj₂ (×-unique ≡-unique (inRange-unique{l = '0'}{'3'}{h₂}) y y₁)

  hourRange? : ∀ h₁ h₂ → Dec (HourRange h₁ h₂)
  hourRange? h₁ h₂ = inRange? '0' '1' h₁ ×-dec inRange? '0' '9' h₂ ⊎-dec toℕ h₁ ≟ toℕ '2' ×-dec inRange? '0' '3' h₂

  asciinum : ∀ {h₁ h₂} → HourRange h₁ h₂ → All (InRange '0' '9') (h₁ ∷ [ h₂ ])
  asciinum (inj₁ x) =
      inRange-relax {B = UInt8} {l = '0'} {'0'} {'1'} {'9'} (proj₁ x) ≤-refl (toWitness{Q = _ ≤? _} tt)
    ∷ proj₂ x
    ∷ []
  asciinum (inj₂ y) =
      ((≤-trans (toWitness{Q = _ ≤? _} tt) (Lemmas.≡⇒≤ (sym $ proj₁ y)))
      , (≤-trans (Lemmas.≡⇒≤ (proj₁ y)) (toWitness{Q = _ ≤? _} tt)))
    ∷ inRange-relax {B = UInt8} {l = '0'} {'0'} {'3'} {'9'} (proj₂ y) ≤-refl (toWitness{Q = _ ≤? _} tt)
    ∷ []

module MinuteRange where
  unambiguous : ∀ {mi₁ mi₂} → (x y : MinuteRange mi₁ mi₂) → x ≡ y
  unambiguous = ×-unique (inRange-unique{B = Dig}{l = '0'}{'5'}) (inRange-unique{B = Dig}{l = '0'}{'9'})

  minuteRange? : ∀ mi₁ mi₂ → Dec (MinuteRange mi₁ mi₂)
  minuteRange? mi₁ mi₂ = inRange? '0' '5' mi₁ ×-dec inRange? '0' '9' mi₂

  asciinum : ∀ {mi₁ mi₂} → MinuteRange mi₁ mi₂ → All (InRange '0' '9') (mi₁ ∷ [ mi₂ ])
  asciinum mr =
      inRange-relax{B = UInt8}{l = '0'}{'0'}{'5'}{'9'} (proj₁ mr) ≤-refl (toWitness{Q = _ ≤? _} tt)
    ∷ proj₂ mr
    ∷ []

module SecRange where
  unambiguous : ∀ {@0 s₁ s₂} → (x y : SecRange s₁ s₂) → x ≡ y
  unambiguous{s₁}{s₂} (inj₁ x) (inj₁ x₁) = ‼ cong (inj₁{B = toℕ s₁ ≡ toℕ '6' × toℕ s₂ ≡ toℕ '0'}) (MinuteRange.unambiguous x x₁)
  unambiguous{s₁}{s₂} (inj₁ (fst₁ , snd₁)) (inj₂ (fst , snd)) =
    contradiction{P = toℕ '6' ≤ toℕ '5'}
      (begin toℕ '6' ≡⟨ sym fst ⟩
             toℕ s₁ ≤⟨ proj₂ fst₁ ⟩
             toℕ '5' ∎)
      (toWitnessFalse{Q = _ ≤? _} tt)
    where
    open ≤-Reasoning
  unambiguous{s₁} (inj₂ (fst , snd)) (inj₁ (fst₁ , snd₁)) =
    contradiction{P = toℕ '6' ≤ toℕ '5'}
      (begin (toℕ '6' ≡⟨ sym fst ⟩
             toℕ s₁ ≤⟨ proj₂ fst₁ ⟩
             toℕ '5' ∎))
      (toWitnessFalse{Q = _ ≤? _} tt)
    where
    open ≤-Reasoning
  unambiguous{s₁}{s₂} (inj₂ y) (inj₂ y₁) =
    ‼ (cong (inj₂{A = MinuteRange s₁ s₂})
         (×-unique ≡-unique ≡-unique y y₁))

  secondRange? : ∀ s₁ s₂ → Dec (SecRange s₁ s₂)
  secondRange? s₁ s₂ = (inRange? '0' '5' s₁ ×-dec inRange? '0' '9' s₂) ⊎-dec toℕ s₁ ≟ toℕ '6' ×-dec toℕ s₂ ≟ toℕ '0'

  asciinum : ∀ {s₁ s₂} → SecRange s₁ s₂ → All (InRange '0' '9') (s₁ ∷ [ s₂ ])
  asciinum (inj₁ x) = MinuteRange.asciinum x
  asciinum (inj₂ y) =
      ((≤-trans (toWitness{Q = _ ≤? _} tt) (Lemmas.≡⇒≤ (sym (proj₁ y))))
      , (≤-trans (Lemmas.≡⇒≤ (proj₁ y)) (toWitness{Q = _ ≤? _} tt)))
    ∷ (Lemmas.≡⇒≤ (sym (proj₂ y)) , ≤-trans (Lemmas.≡⇒≤ (proj₂ y)) (toWitness{Q = _ ≤? _} tt))
    ∷ []

module MonthDayHourMinSecFields where
  @0 unambiguous : Unambiguous MonthDayHourMinSecFields
  unambiguous (mkMDHMSFields{mo₁}{mo₂}{d₁}{d₂}{h₁}{h₂}{mi₁}{mi₂}{s₁}{s₂} mon monRange day dayRange hour hourRange min minRange sec secRange bs≡) (mkMDHMSFields{mo₁'}{mo₂'}{d₁'}{d₂'}{h₁'}{h₂'}{mi₁'}{mi₂'}{s₁'}{s₂'} mon₁ monRange₁ day₁ dayRange₁ hour₁ hourRange₁ min₁ minRange₁ sec₁ secRange₁ bs≡₁) =
    subst₂ (λ m1 m2 → ∀ mon₁ monRange₁ bs≡₁ → _ ≡ mkMDHMSFields{mo₁ = m1}{m2} mon₁ monRange₁ _ _ _ _ _ _ _ _ bs≡₁ )
      mo₁≡ mo₂≡
      (λ mon₁ monRange₁ bs≡₁ →
        subst₂ (λ d₁' d₂' → ∀ day₁ dayRange₁ bs≡₁ → _ ≡ mkMDHMSFields {d₁ = d₁'} {d₂'} _ _ day₁ dayRange₁ _ _ _ _ _ _ bs≡₁)
          d₁≡ d₂≡
          (λ day₁ dayRange₁ bs≡₁ →
            subst₂ (λ h₁' h₂' → ∀ hour₁ hourRange₁ bs≡₁ → _ ≡ mkMDHMSFields{h₁ = h₁'}{h₂'} _ _ _ _ hour₁ hourRange₁ _ _ _ _ bs≡₁)
              h₁≡ h₂≡
              (λ hour₁ hourRange₁ bs≡₁ →
                subst₂ (λ mi₁' mi₂' → ∀ min₁ minRange₁ bs≡₁ → _ ≡ mkMDHMSFields{mi₁ = mi₁'}{mi₂'} _ _ _ _ _ _ min₁ minRange₁ _ _ bs≡₁)
                  mi₁≡ mi₂≡
                  (λ min₁ minRange₁ bs≡₁ →
                    subst₂ (λ s₁' s₂' → ∀ sec₁ secRange₁ bs≡₁ → _ ≡ mkMDHMSFields{s₁ = s₁'}{s₂'} _ _ _ _ _ _ _ _ sec₁ secRange₁ bs≡₁) s₁≡ s₂≡
                      (λ sec₁ secRange₁ bs≡₁ →
                        subst₂ (λ mon₁ monRange₁ → _ ≡ mkMDHMSFields mon₁ monRange₁ _ _ _ _ _ _ _ _ _) (uniqueSingleton mon mon₁) (MonthRange.unambiguous monRange monRange₁)
                          (subst₂ (λ day₁ dayRange₁ → _ ≡ mkMDHMSFields _ _  day₁ dayRange₁ _ _ _ _ _ _ _) (uniqueSingleton day day₁) (DayRange.unambiguous dayRange dayRange₁)
                            (subst₂ (λ hour₁ hourRange₁ → _ ≡ mkMDHMSFields _ _ _ _ hour₁ hourRange₁ _ _ _ _ _) (uniqueSingleton hour hour₁) (HourRange.unambiguous hourRange hourRange₁)
                              (subst₂ (λ min₁ minRange₁ → _ ≡ mkMDHMSFields _ _ _ _ _ _ min₁ minRange₁ _ _ _) (uniqueSingleton min min₁) (MinuteRange.unambiguous minRange minRange₁)
                                (subst₂ (λ sec₁ secRange₁ → _ ≡ mkMDHMSFields _ _ _ _ _ _ _ _ sec₁ secRange₁ _) (uniqueSingleton sec sec₁) (SecRange.unambiguous secRange secRange₁)
                                  (subst (λ bs≡₁ → _ ≡ mkMDHMSFields _ _ _ _ _ _ _ _ _ _ bs≡₁) (≡-unique bs≡ bs≡₁) refl))))))
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

  @0 nosubstrings : NoSubstrings MonthDayHourMinSecFields
  nosubstrings {xs₁ = xs₁} {xs₂ = xs₂} x (mkMDHMSFields mon monRange day dayRange hour hourRange min minRange sec secRange bs≡) (mkMDHMSFields mon₁ monRange₁ day₁ dayRange₁ hour₁ hourRange₁ min₁ minRange₁ sec₁ secRange₁ bs≡₁)
    with Lemmas.length-++-≡ xs₁ _ xs₂ _ x (trans₀ (cong length bs≡) (cong length (sym bs≡₁)))
  ... | fst , snd = fst

  instance
    eqMonthDayHourMinSecFields : Eq (Exists─ (List UInt8) MonthDayHourMinSecFields)
    Eq._≟_ eqMonthDayHourMinSecFields
      (─ bs  , mkMDHMSFields{mo₁}{mo₂}{d₁}{d₂}{h₁}{h₂}{mi₁}{mi₂}{s₁}{s₂}
                 (singleton mon mon≡) monRange
                 (singleton day day≡) dayRange
                 (singleton hour hour≡) hourRange
                 (singleton min min≡) minRange
                 (singleton sec sec≡) secRange
                 refl)
      (─ bs₁ , mkMDHMSFields{mo₁'}{mo₂'}{d₁'}{d₂'}{h₁'}{h₂'}{mi₁'}{mi₂'}{s₁'}{s₂'}
                 (singleton mon₁ mon≡₁) monRange₁
                 (singleton day₁ day≡₁) dayRange₁
                 (singleton hour₁ hour≡₁) hourRange₁
                 (singleton min₁ min≡₁) minRange₁
                 (singleton sec₁ sec≡₁) secRange₁
                 refl) =
      case mon ≟ mon₁ ret (const _) of λ where
        (no ¬eq) → no λ where refl → contradiction refl ¬eq
        (yes refl) →
          case (─ asciiNum-injective (mo₁ ∷ [ mo₂ ]) (mo₁' ∷ [ mo₂' ])
                    (MonthRange.monthRange⇒asciinum monRange) (MonthRange.monthRange⇒asciinum monRange₁)
                    refl (trans (sym mon≡) mon≡₁))
          ret (const _) of λ where
            (─ refl) →
              case (─ ≡-unique mon≡ mon≡₁ ,′ ─ MonthRange.unambiguous monRange monRange₁)
              ret (const _) of λ where
                (─ refl , ─ refl) →
                  case day ≟ day₁ ret (const _) of λ where
                    (no ¬eq)   → no λ where refl → contradiction refl ¬eq
                    (yes refl) →
                      case ─ asciiNum-injective (d₁ ∷ [ d₂ ]) (d₁' ∷ [ d₂' ])
                                 (DayRange.asciinum dayRange) (DayRange.asciinum dayRange₁)
                                 refl (trans (sym day≡) day≡₁)
                      ret (const _) of λ where
                        (─ refl) →
                          case (─ ≡-unique day≡ day≡₁ ,′ ─ DayRange.unambiguous dayRange dayRange₁) ret (const _) of λ where
                            (─ refl , ─ refl) →
                              case hour ≟ hour₁ of λ where
                                (no ¬eq)   → no λ where refl → contradiction refl ¬eq
                                (yes refl) →
                                  case ─ asciiNum-injective (h₁ ∷ [ h₂ ]) (h₁' ∷ [ h₂' ])
                                    (HourRange.asciinum hourRange) (HourRange.asciinum hourRange₁)
                                    refl (trans (sym hour≡) hour≡₁)
                                  ret (const _) of λ where
                                    (─ refl) →
                                      case (─ ≡-unique hour≡ hour≡₁ ,′ ─ HourRange.unambiguous hourRange hourRange₁)
                                      ret (const _) of λ where
                                        (─ refl , ─ refl) →
                                          case min ≟ min₁ of λ where
                                            (no ¬eq)   → no λ where refl → contradiction refl ¬eq
                                            (yes refl) →
                                              case ─ asciiNum-injective (mi₁ ∷ [ mi₂ ]) (mi₁' ∷ [ mi₂' ])
                                                (MinuteRange.asciinum minRange) (MinuteRange.asciinum minRange₁)
                                                refl (trans (sym min≡) min≡₁)
                                              ret (const _) of λ where
                                                (─ refl) →
                                                  case (─ ≡-unique min≡ min≡₁ ,′ ─ MinuteRange.unambiguous minRange minRange₁)
                                                  ret (const _) of λ where
                                                    (─ refl , ─ refl) →
                                                      case sec ≟ sec₁ of λ where
                                                        (no ¬eq)   → no λ where refl → contradiction refl ¬eq
                                                        (yes refl) →
                                                          case ─ asciiNum-injective (s₁ ∷ [ s₂ ]) (s₁' ∷ [ s₂' ])
                                                            (SecRange.asciinum secRange) (SecRange.asciinum secRange₁)
                                                            refl (trans (sym sec≡) sec≡₁)
                                                          ret (const _)
                                                          of λ where
                                                            (─ refl) →
                                                              case (─ ≡-unique sec≡ sec≡₁ ,′ ─ SecRange.unambiguous secRange secRange₁)
                                                              ret (const _) of λ where
                                                                (─ refl , ─ refl) →
                                                                  yes refl
      where
      open ≡-Reasoning

module UTC where
  instance
    eqUTC : Eq (Exists─ (List UInt8) UTCTimeFields)
    Eq._≟_ eqUTC
      (─ bs₁ , mkUTCTimeFields{y₁}{y₂}
                 (singleton year year≡) yearRange
                 mmddhhmmss refl refl)
      (─ bs₂ , mkUTCTimeFields{y₁'}{y₂'}
                 (singleton year₁ year₁≡) yearRange₁
                 mmddhhmmss₁ refl refl) =
      case year ≟ year₁ of λ where
        (no ¬eq)   → no λ where refl → contradiction refl ¬eq
        (yes refl) →
          case (─ asciiNum-injective
                    (y₁ ∷ [ y₂ ]) (y₁' ∷ [ y₂' ])
                    yearRange yearRange₁
                    refl (trans (sym year≡) year₁≡))
          ret (const _) of λ where
            (─ refl) →
              case (─ ≡-unique year≡ year₁≡ ,′ ─ All.irrelevant (inRange-unique{A = Char}{B = UInt8}{l = '0'}{u = '9'}) yearRange yearRange₁) ret (const _) of λ where
                (─ refl , ─ refl) →
                  case (─ _ , mmddhhmmss) ≟ (─ _ , mmddhhmmss₁) ret (const _) of λ where
                    (no ¬eq) → no λ where refl → contradiction refl ¬eq
                    (yes refl) → yes refl

  @0 nosubstrings : NoSubstrings UTCTimeFields
  nosubstrings {xs₁ = xs₁} {xs₂ = xs₂} x (mkUTCTimeFields year yearRange mmddhhmmss term bs≡) (mkUTCTimeFields year₁ yearRange₁ mmddhhmmss₁ term₁ bs≡₁)
    with Lemmas.length-++-≡ xs₁ _ xs₂ _ x (trans₀ (cong length bs≡) (cong length (sym bs≡₁)))
  ... | fst , snd = fst

  @0 unambiguous : Unambiguous UTCTimeFields
  unambiguous (mkUTCTimeFields{y1 = y1}{y2}{mn1}{mn2}{d1}{d2}{h1}{h2}{mi1}{mi2}{s1}{s2} year yearRange mmddhhmmss refl bs≡) (mkUTCTimeFields{y1 = y1'}{y2'}{mn1'}{mn2'}{d1'}{d2'}{h1'}{h2'}{mi1'}{mi2'}{s1'}{s2'} year₁ yearRange₁ mmddhhmmss₁ refl bs≡₁) =
    subst₂
      ((λ y1“ y2“ → ∀ (year₁ : Singleton (asciiNum (y1“ ∷ [ y2“ ]))) (yearRange₁ : All (InRange '0' '9') (y1“ ∷ [ y2“ ])) bs≡
        → _ ≡ mkUTCTimeFields year₁ yearRange₁ mmddhhmmss₁ refl bs≡))
      y1≡ y2≡
      (λ year₁ yearRange₁ bs≡₁' →
        subst₂
          (λ mn1“ mn2“ →
            ∀ (mmddhhmmss₁ : MonthDayHourMinSecFields ((mn1“ ∷ mn2“ ∷ d1' ∷ d2' ∷ h1' ∷ h2' ∷ mi1' ∷ mi2' ∷ s1' ∷ [ s2' ]))) bs≡₁ →
            _ ≡ mkUTCTimeFields year₁ yearRange₁ mmddhhmmss₁ _ bs≡₁ )
          mn1≡ mn2≡
          (λ mmddhhmmss₁ bs≡₁' →
            subst₂
              (λ d1“ d2“ → ∀ (mmddhhmmss₁ : MonthDayHourMinSecFields ((mn1 ∷ mn2 ∷ d1“ ∷ d2“ ∷ h1' ∷ h2' ∷ mi1' ∷ mi2' ∷ s1' ∷ [ s2' ]))) bs≡₁ →
                _ ≡ mkUTCTimeFields year₁ yearRange₁ mmddhhmmss₁ _ bs≡₁)
              d1≡ d2≡
              (λ mmddhhmmss₁ bs≡₁' →
                subst₂
                  (λ h1“ h2“ → ∀ (mmddhhmmss₁ : MonthDayHourMinSecFields ((mn1 ∷ mn2 ∷ d1 ∷ d2 ∷ h1“ ∷ h2“ ∷ mi1' ∷ mi2' ∷ s1' ∷ [ s2' ]))) bs≡₁ →
                    _ ≡ mkUTCTimeFields year₁ yearRange₁ mmddhhmmss₁ _ bs≡₁)
                  h1≡ h2≡
                  (λ mmddhhmmss₁ bs≡₁' →
                    subst₂
                      (λ mi1“ mi2“ → ∀ (mmddhhmmss₁ : MonthDayHourMinSecFields ((mn1 ∷ mn2 ∷ d1 ∷ d2 ∷ h1 ∷ h2 ∷ mi1“ ∷ mi2“ ∷ s1' ∷ [ s2' ]))) bs≡₁ →
                        _ ≡ mkUTCTimeFields year₁ yearRange₁ mmddhhmmss₁ _ bs≡₁)
                      mi1≡ mi2≡
                      (λ mmddhhmmss₁ bs≡₁' →
                        subst₂
                          (λ s1“ s2“ → ∀ (mmddhhmmss₁ : MonthDayHourMinSecFields ((mn1 ∷ mn2 ∷ d1 ∷ d2 ∷ h1 ∷ h2 ∷ mi1 ∷ mi2 ∷ s1“ ∷ [ s2“ ]))) bs≡₁ →
                            _ ≡ mkUTCTimeFields year₁ yearRange₁ mmddhhmmss₁ _ bs≡₁)
                          s1≡ s2≡
                          (λ mmddhhmmss₁ bs≡₁' →
                            subst₂
                              (λ year₁ yearRange₁ → _ ≡ mkUTCTimeFields year₁ yearRange₁ mmddhhmmss₁ _ bs≡₁')
                              (uniqueSingleton year _) (All.irrelevant (×-unique ≤-irrelevant ≤-irrelevant) yearRange yearRange₁)
                              (subst₂
                                (λ mmddhhmmss₁ bs≡₁' →
                                  _ ≡ mkUTCTimeFields year yearRange mmddhhmmss₁ _ bs≡₁')
                                (MonthDayHourMinSecFields.unambiguous mmddhhmmss mmddhhmmss₁) (≡-unique bs≡ bs≡₁') refl))
                          mmddhhmmss₁ bs≡₁')
                      mmddhhmmss₁ bs≡₁')
                  mmddhhmmss₁ bs≡₁')
              mmddhhmmss₁ bs≡₁')
          mmddhhmmss₁ bs≡₁')
      year₁ yearRange₁ bs≡₁
    where
    @0 bs≡' : y1 ∷ y2 ∷ mn1 ∷ mn2 ∷ d1 ∷ d2 ∷ h1 ∷ h2 ∷ mi1 ∷ mi2 ∷ s1 ∷ s2 ∷ [ # 'Z' ] ≡ y1' ∷ y2' ∷ mn1' ∷ mn2' ∷ d1' ∷ d2' ∷ h1' ∷ h2' ∷ mi1' ∷ mi2' ∷ s1' ∷ s2' ∷ [ # 'Z' ]
    bs≡' = trans₀ (sym bs≡) bs≡₁

    @0 y1≡ : y1 ≡ y1'
    y1≡ = ∷-injectiveˡ bs≡'

    @0 y2≡ : y2 ≡ y2'
    y2≡ = ∷-injectiveˡ (proj₂ (Lemmas.length-++-≡ [ _ ] _ [ _ ] _ bs≡' refl))

    @0 mn1≡ : mn1 ≡ mn1'
    mn1≡ = ∷-injectiveˡ (proj₂ (Lemmas.length-++-≡ (_ ∷ [ _ ]) _ (_ ∷ [ _ ]) _ bs≡' refl))

    @0 mn2≡ : mn2 ≡ mn2'
    mn2≡ = ∷-injectiveˡ (proj₂ (Lemmas.length-++-≡ (_ ∷ _ ∷ [ _ ]) _ (_ ∷ _ ∷ [ _ ]) _ bs≡' refl))

    @0 d1≡ : d1 ≡ d1'
    d1≡ = ∷-injectiveˡ (proj₂ (Lemmas.length-++-≡ (_ ∷ _ ∷ _ ∷ [ _ ]) _ (_ ∷ _ ∷ _ ∷ [ _ ]) _ bs≡' refl))

    @0 d2≡ : d2 ≡ d2'
    d2≡ = ∷-injectiveˡ (proj₂ (Lemmas.length-++-≡ (_ ∷ _ ∷ _ ∷ _ ∷ [ _ ]) _ (_ ∷ _ ∷ _ ∷ _ ∷ [ _ ]) _ bs≡' refl))

    @0 h1≡ : h1 ≡ h1'
    h1≡ = ∷-injectiveˡ (proj₂ (Lemmas.length-++-≡ (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ [ _ ]) _ (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ [ _ ]) _ bs≡' refl))

    @0 h2≡ : h2 ≡ h2'
    h2≡ = ∷-injectiveˡ (proj₂ (Lemmas.length-++-≡ (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ [ _ ]) _ (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ [ _ ]) _ bs≡' refl))

    @0 mi1≡ : mi1 ≡ mi1'
    mi1≡ = ∷-injectiveˡ (proj₂ (Lemmas.length-++-≡ (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ [ _ ]) _ (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ [ _ ]) _ bs≡' refl))

    @0 mi2≡ : mi2 ≡ mi2'
    mi2≡ = ∷-injectiveˡ (proj₂ (Lemmas.length-++-≡ (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ [ _ ]) _ (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ [ _ ]) _ bs≡' refl))

    @0 s1≡ : s1 ≡ s1'
    s1≡ = ∷-injectiveˡ (proj₂ (Lemmas.length-++-≡ (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ [ _ ]) _ (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ [ _ ]) _ bs≡' refl))

    @0 s2≡ : s2 ≡ s2'
    s2≡ = ∷-injectiveˡ (proj₂ (Lemmas.length-++-≡ (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ [ _ ]) _ (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ [ _ ]) _ bs≡' refl))

module GenTime where
  instance
    eqGenTime : Eq (Exists─ (List UInt8) GenTimeFields)
    Eq._≟_ eqGenTime
      (─ bs₁ , mkGenTimeFields{y₁}{y₂}{y₃}{y₄}
                 (singleton year year≡) yearRange
                 mmddhhmmss refl refl)
      (─ bs₂ , mkGenTimeFields{y₁'}{y₂'}{y₃'}{y₄'}
                 (singleton year₁ year₁≡) yearRange₁
                 mmddhhmmss₁ refl refl) =
      case year ≟ year₁ of λ where
        (no ¬eq)   → no λ where refl → contradiction refl ¬eq
        (yes refl) →
          case (─ asciiNum-injective
                    (y₁ ∷ y₂ ∷ y₃ ∷ [ y₄ ]) (y₁' ∷ y₂' ∷ y₃' ∷ [ y₄' ])
                    yearRange yearRange₁
                    refl (trans (sym year≡) year₁≡))
          ret (const _) of λ where
            (─ refl) →
              case (─ ≡-unique year≡ year₁≡ ,′ ─ All.irrelevant (inRange-unique{A = Char}{B = UInt8}{l = '0'}{u = '9'}) yearRange yearRange₁) ret (const _) of λ where
                (─ refl , ─ refl) →
                  case (─ _ , mmddhhmmss) ≟ (─ _ , mmddhhmmss₁) ret (const _) of λ where
                    (no ¬eq) → no λ where refl → contradiction refl ¬eq
                    (yes refl) → yes refl

  @0 nosubstrings : NoSubstrings GenTimeFields
  nosubstrings {xs₁ = xs₁} {xs₂ = xs₂} x (mkGenTimeFields year yearRange (mkMDHMSFields mon monRange day dayRange hour hourRange min minRange sec secRange refl) z≡ bs≡) (mkGenTimeFields year₁ yearRange₁ (mkMDHMSFields mon₁ monRange₁ day₁ dayRange₁ hour₁ hourRange₁ min₁ minRange₁ sec₁ secRange₁ refl) z≡₁ bs≡₁)
    with Lemmas.length-++-≡ xs₁ _ xs₂ _ x (trans₀ (cong length bs≡) (cong length (sym bs≡₁)))
  ... | fst , snd = fst

  @0 unambiguous : Unambiguous GenTimeFields
  unambiguous (mkGenTimeFields{y1 = y1}{y2}{y3}{y4}{z}{mdhms} year yearRange mmddhhmmss refl bs≡) (mkGenTimeFields{y1 = y1'}{y2'}{y3'}{y4'}{z'}{mdhms'} year₁ yearRange₁ mmddhhmmss₁ refl bs≡₁) =
    subst₂
      (λ y1“ y2“ → ∀ (year₁ : Singleton (asciiNum (y1“ ∷ y2“ ∷ y3' ∷ [ y4' ]))) (yearRange₁ : All (InRange '0' '9') (y1“ ∷ y2“ ∷ y3' ∷ [ y4' ])) bs≡₁
        → _ ≡ mkGenTimeFields year₁ yearRange₁ mmddhhmmss₁ refl bs≡₁)
      y1≡ y2≡
      (λ year₁ yearRange₁ bs≡₁ →
        subst₂ (λ y3“ y4“ → ∀ (year₁ : Singleton (asciiNum (y1 ∷ y2 ∷ y3“ ∷ [ y4“ ]))) (yearRange₁ : All (InRange '0' '9') (y1 ∷ y2 ∷ y3“ ∷ [ y4“ ])) bs≡₁ →
          _ ≡ mkGenTimeFields year₁ yearRange₁ mmddhhmmss₁ refl bs≡₁)
          y3≡ y4≡
          (λ year₁ yearRange₁ bs≡₁ →
            subst (λ mdhms“ → ∀ (mmddhhmmss₁ : MonthDayHourMinSecFields mdhms“) bs≡₁ → _ ≡ mkGenTimeFields year₁ yearRange₁ mmddhhmmss₁ refl bs≡₁) mdhms≡
              (λ mmddhhmmss₁ bs≡₁ →
                subst₂ (λ year₁ yearRange₁ → _ ≡ mkGenTimeFields year₁ yearRange₁ mmddhhmmss₁ refl bs≡₁)
                  (uniqueSingleton year _) (All.irrelevant (×-unique ≤-irrelevant ≤-irrelevant) yearRange yearRange₁)
                    (subst₂
                      (λ mmddhhmmss₁ bs≡₁ → _ ≡ mkGenTimeFields _ _ mmddhhmmss₁ _ bs≡₁)
                      (MonthDayHourMinSecFields.unambiguous mmddhhmmss _) (≡-unique bs≡ bs≡₁) refl))
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

  serialLength : ∀ {bs} → GenTimeFields bs → length bs ≡ 15
  serialLength{bs} (mkGenTimeFields{y₁}{y₂}{y₃}{y₄} year yearRange (mkMDHMSFields{mo₁}{mo₂}{d₁}{d₂}{h₁}{h₂}{mi₁}{mi₂}{s₁}{s₂} mon monRange day dayRange hour hourRange min minRange sec secRange refl) refl bs≡) =
    ‼ (begin length bs ≡⟨ cong length bs≡ ⟩
             length (y₁ ∷ y₂ ∷ y₃ ∷ y₄ ∷ (mo₁ ∷ mo₂ ∷ d₁ ∷ d₂ ∷ h₁ ∷ h₂ ∷ mi₁ ∷ mi₂ ∷ s₁ ∷ [ s₂ ]) ∷ʳ (# 'Z')) ∎)
    where open ≡-Reasoning

@0 nosubstrings : NoSubstrings Time
nosubstrings x (utctm x₁) (utctm x₂) = ‼ TLV.nosubstrings x x₁ x₂
nosubstrings x (utctm x₁) (gentm x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (gentm x₁) (utctm x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nosubstrings x (gentm x₁) (gentm x₂) = ‼ TLV.nosubstrings x x₁ x₂

@0 unambiguous : Unambiguous Time
unambiguous (utctm x) (utctm x₁) = cong utctm $ TLV.unambiguous UTC.unambiguous x x₁
unambiguous (utctm x) (gentm x₁) = ⊥-elim (TLV.noconfusion (λ ()) (cong (_++ []) refl) x x₁)
unambiguous (gentm x) (utctm x₁) = ⊥-elim (TLV.noconfusion (λ ()) (cong (_++ []) refl) x x₁)
unambiguous (gentm x) (gentm x₁) = cong gentm $ TLV.unambiguous GenTime.unambiguous x x₁

instance
  eqTime : Eq (Exists─ (List UInt8) Time)
  (eqTime Eq.≟ (─ bs₁ , utctm x)) (─ bs₂ , utctm x₁) =
    case (─ _ , x) ≟ (─ _ , x₁) of λ where
      (no ¬eq)   → no λ where refl → contradiction refl ¬eq
      (yes refl) → yes refl

  (eqTime Eq.≟ (─ bs₁ , utctm x)) (─ bs₂ , gentm x₁) = no λ ()
  (eqTime Eq.≟ (─ bs₁ , gentm x)) (─ bs₂ , utctm x₁) = no λ ()
  (eqTime Eq.≟ (─ bs₁ , gentm x)) (─ bs₂ , gentm x₁) =
    case (─ _ , x) ≟ (─ _ , x₁) of λ where
      (no ¬eq) → no λ where refl → contradiction refl ¬eq
      (yes refl) → yes refl
