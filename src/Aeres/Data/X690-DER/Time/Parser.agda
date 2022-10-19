{-# OPTIONS --subtyping --inversion-max-depth=100 #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X690-DER.TLV
open import Aeres.Data.X690-DER.Time.Properties
open import Aeres.Data.X690-DER.Time.TCB
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parser
open import Data.List.Properties
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X690-DER.Time.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parser      UInt8

module parseMonthDayHourMinSecFields where
  here' = "parseMonthDayHourMinSecFields"

  parseMonthDayHourMinSecFields : Parser (Logging ∘ Dec) MonthDayHourMinSecFields
  runParser parseMonthDayHourMinSecFields xs = do
    yes (success pre₀@._ ._ refl (mk×ₚ (singleton (mn1 ∷ mn2 ∷ d1 ∷ d2 ∷ h1 ∷ h2 ∷ mi1 ∷ mi2 ∷ s1 ∷ s2 ∷ []) refl) (─ refl) refl) suf₀ refl)
      ← runParser (parseN (String.length "MMDDhhmmss") (tell $ here' String.++ ": underflow")) xs
      where no ¬parse → do
        return ∘ no $ λ where
          (success prefix@._ _ _ (mkMDHMSFields _ _ _ _ _ _ _ _ _ _ refl) suffix ps≡) →
            contradiction
              (success prefix _ refl (mk×ₚ singleSelf (─ refl) refl) suffix ps≡)
              ¬parse
    case check mn1 mn2 d1 d2 h1 h2 mi1 mi2 s1 s2 suf₀ of λ where
      (l , no  ¬check) → do
        tell $ here' String.++ ": range check failed " String.++ l
        return (no ¬check)
      (_ , yes ✓check) →
        return (yes ✓check)
    where
    check : ∀ mn1 mn2 d1 d2 h1 h2 mi1 mi2 s1 s2 suf₀
            → String × Dec (Success MonthDayHourMinSecFields (mn1 ∷ mn2 ∷ d1 ∷ d2 ∷ h1 ∷ h2 ∷ mi1 ∷ mi2 ∷ s1 ∷ s2 ∷ suf₀))
    check mn1 mn2 d1 d2 h1 h2 mi1 mi2 s1 s2 suf₀
      with mn1 ≟ # '0' ×-dec inRange? '0' '9' mn2 ⊎-dec mn1 ≟ # '1' ×-dec inRange? '0' '2' mn2
    ... | no ¬mnᵣ = "month" ,  no λ where
      (success ._ ._ refl (mkMDHMSFields _ monRange _ _ _ _ _ _ _ _ refl) ._ refl) →
        contradiction monRange ¬mnᵣ
    ... | yes mnᵣ
      with inRange? '0' '2' d1 ×-dec inRange? '0' '9' d2 ⊎-dec toℕ d1 ≟ toℕ '3' ×-dec inRange? '0' '1' d2
    ... | no ¬dᵣ = "day" , no λ where
      (success ._ ._ refl (mkMDHMSFields _ _ _ dayRange _ _ _ _ _ _ refl) ._ refl) →
        contradiction dayRange ¬dᵣ
    ... | yes dᵣ
      with inRange? '0' '1' h1 ×-dec inRange? '0' '9' h2 ⊎-dec toℕ h1 ≟ toℕ '2' ×-dec inRange? '0' '3' h2
    ... | no ¬hᵣ = "hour" , no λ where
      (success ._ ._ refl (mkMDHMSFields _ _ _ _ _ hourRange _ _ _ _ refl) ._ refl) →
        contradiction hourRange ¬hᵣ
    ... | yes hᵣ
      with inRange? '0' '5' mi1 ×-dec inRange? '0' '9' mi2
    ... | no ¬miᵣ = "min" , no λ where
      (success ._ ._ refl (mkMDHMSFields _ _ _ _ _ _ _ minRange _ _ refl) ._ refl) →
        contradiction minRange ¬miᵣ
    ... | yes miᵣ
      with (inRange? '0' '5' s1 ×-dec inRange? '0' '9' s2) ⊎-dec (toℕ s1 ≟ toℕ '6' ×-dec toℕ s2 ≟ toℕ '0')
    ... | no ¬sᵣ = "sec" , no λ where
      (success ._ ._ refl (mkMDHMSFields _ _ _ _ _ _ _ _ _ secRange refl) ._ refl) →
        contradiction secRange ¬sᵣ
    ... | yes sᵣ =
      "" , yes (success _ _ refl
        (mkMDHMSFields singleSelf mnᵣ singleSelf dᵣ singleSelf hᵣ singleSelf miᵣ singleSelf sᵣ refl)
        suf₀ refl)

open parseMonthDayHourMinSecFields public using (parseMonthDayHourMinSecFields)

module parseUTCTimeFields where

  here' = "parseUTCTimeFields"
  open ≡-Reasoning

  parseUTCTimeFields : Parser (Logging ∘ Dec) UTCTimeFields
  runParser parseUTCTimeFields xs = do
    yes (success ._ ._ refl (mk×ₚ (singleton (y₁ ∷ y₂ ∷ []) refl) (─ refl) refl) suf₀ refl)
      ← runParser (parseN (String.length "YY") (tell $ here' String.++ ": underflow")) xs
      where no ¬parse → do
        return ∘ no $ λ where
          (success prefix@._ read read≡ (mkUTCTimeFields{y1 = y₁}{y₂} _ _ _ _ refl) suffix ps≡) →
            contradiction
              (success (y₁ ∷ [ y₂ ]) 2 refl (mk×ₚ singleSelf (─ refl) refl) _ ps≡)
              ¬parse
    yes (success pre₁@._ r₁ r₁≡ v₁@(mkMDHMSFields mon monᵣ day dayᵣ hour hourᵣ min minᵣ sec secᵣ refl) suf₁ ps≡₁)
      ← runParser parseMonthDayHourMinSecFields suf₀
      where no ¬parse → do
        tell $ here'
        return ∘ no $ λ where
          (success prefix read read≡ (mkUTCTimeFields{y1 = y₁'}{y₂'}{z = z} year yearRange mmddhhmmss term refl) suffix ps≡) → ‼
            let @0 y₁≡ : y₁' ≡ y₁
                y₁≡ = ∷-injectiveˡ ps≡

                @0 y₂≡ : y₂' ≡ y₂
                y₂≡ = ∷-injectiveˡ (∷-injectiveʳ ps≡)

                @0 ps≡' : _
                ps≡' = trans (sym ps≡) (trans (cong (_∷ _) y₁≡) (cong (λ x → y₁ ∷ x ∷ _) y₂≡))
            in
            contradiction
              (success _ _ refl mmddhhmmss (z ∷ suffix) (sym (++-cancelˡ (y₁ ∷ [ y₂ ]) ps≡')))
              ¬parse
    yes (success ._ 1 refl refl suf₂ refl)
      ← runParser (parseLit (tell $ here' String.++ ": underflow") (tell $ here' String.++ ": mismatch") [ # toℕ 'Z' ]) suf₁
      where no ¬parse → do
        return ∘ no $ λ where
          (success prefix@._ read read≡ (mkUTCTimeFields{y1 = y₁'}{y₂'}{z = z} year yearRange mmddhhmmss term refl) suffix ps≡) → ‼
            let @0 ps≡' : _
                ps≡' = proj₂ $
                  Lemmas.length-++-≡
                    (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ [ _ ]) (z ∷ suffix)
                    (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ [ _ ]) suf₁
                    (trans (proj₂ $ Lemmas.length-++-≡ (y₁' ∷ [ y₂' ]) _ (y₁ ∷ [ y₂ ]) _ ps≡ refl)
                      (sym ps≡₁))
                    refl
            in
            contradiction
              (success [ z ] _ refl (cong (_∷ []) term) suffix ps≡')
              ¬parse
    case All.all? (inRange? '0' '9') (y₁ ∷ [ y₂ ]) of λ where
      (no ¬yᵣ) → do
        tell $ here' String.++ ": invalid range for year"
        return ∘ no $ λ where
          (success prefix read read≡ (mkUTCTimeFields{y1 = y₁'}{y₂'} year yearRange _ _ refl) suffix ps≡) →
            contradiction
              (subst (All (InRange '0' '9')) (proj₁ $ Lemmas.length-++-≡ _ _ _ _ ps≡ refl) yearRange)
              ¬yᵣ
      (yes yᵣ) →
        return (yes
          (success (y₁ ∷ y₂ ∷ pre₁ ++ [ # toℕ 'Z' ])
            (2 + r₁ + 1)
            (cong (2 +_) (begin r₁ + 1 ≡⟨ cong (_+ 1) r₁≡ ⟩
                                11     ∎))
            (mkUTCTimeFields singleSelf yᵣ v₁ refl refl)
            suf₂
            (cong (λ x → y₁ ∷ y₂ ∷ x) ps≡₁)))

open parseUTCTimeFields public using (parseUTCTimeFields)

parseUTCTime : Parser (Logging ∘ Dec) UTCTime
parseUTCTime =
  parseTLV _ "UTCTime" _
    (parseExactLength UTC.nonnesting (tell $ "UTCTime: length mismatch") parseUTCTimeFields)

module parseGenTimeFields where
  open ≡-Reasoning

  here' = "parseGenTimeFields"

  parseGenTimeFields : Parser (Logging ∘ Dec) GenTimeFields
  runParser parseGenTimeFields xs = do
    yes (success .v₀ r₀ r₀≡ (mk×ₚ (singleton v₀@(y₁ ∷ y₂ ∷ y₃ ∷ y₄ ∷ []) refl) vLen refl) suf₀ ps≡₀)
      ← runParser (parseN (String.length "YYYY") (tell $ here' String.++ ": underflow")) xs
      where no ¬parse → do
        return ∘ no $ λ where
          (success ._ read read≡ (mkGenTimeFields{y1 = y₁}{y₂}{y₃}{y₄} year _ _ _ refl) suffix ps≡) →
            contradiction
              (success (y₁ ∷ y₂ ∷ y₃ ∷ [ y₄ ]) _ refl (mk×ₚ singleSelf (─ refl) refl) _ ps≡)
              ¬parse
    yes (success pre₁ r₁ r₁≡ v₁ suf₁ ps≡₁) ← runParser parseMonthDayHourMinSecFields suf₀
      where no ¬parse → do
        tell here'
        return ∘ no $ λ where
          (success prefix@._ read read≡ (mkGenTimeFields{y1 = y₁'}{y₂'}{y₃'}{y₄'}{z}{mdhms} year yearRange mmddhhmmss z≡ refl) suffix ps≡) → ‼
            let @0 ps≡' : v₀ ++ suf₀ ≡ y₁' ∷ y₂' ∷ y₃' ∷ y₄' ∷ mdhms ∷ʳ z ++ suffix
                ps≡' = trans ps≡₀ (sym ps≡)
            in
            contradiction
              (success _ _ refl mmddhhmmss (z ∷ suffix)
                (begin (mdhms ++ z ∷ suffix
                         ≡⟨ solve (++-monoid UInt8) ⟩
                       (mdhms ∷ʳ z) ++ suffix
                         ≡⟨ (proj₂ $ Lemmas.length-++-≡ (y₁' ∷ y₂' ∷ y₃' ∷ [ y₄' ]) _ _ _ (sym ps≡') refl) ⟩
                       suf₀ ∎)))
              ¬parse
    yes (success pre₂ ._ refl refl suf₂ ps≡₂)
      ← runParser (parseLit (tell $ here' String.++ ": underflow") (tell $ here' String.++ ": mismatch (Z)") [ # 'Z' ]) suf₁
      where no ¬parse → do
        return ∘ no $ λ where
          (success ._ read read≡ (mkGenTimeFields{y1 = y₁'}{y₂'}{y₃'}{y₄'}{z}{mdhms} year yearRange mmddhhmmss refl refl) suffix ps≡) → ‼
            let @0 ps≡' : v₀ ++ pre₁ ++ suf₁ ≡ y₁' ∷ y₂' ∷ y₃' ∷ y₄' ∷ mdhms ∷ʳ z ++ suffix
                ps≡' = trans (cong (λ x → _ ∷ _ ∷ _ ∷ _ ∷ x) ps≡₁) (trans ps≡₀ (sym ps≡)) -- trans ps≡₀ (sym ps≡)

                @0 ps≡″ : pre₁ ++ suf₁ ≡ mdhms ++ [ z ] ++ suffix
                ps≡″ = trans₀ (Lemmas.++-cancel≡ˡ _ _ (proj₁ $ Lemmas.length-++-≡ v₀ _ (y₁' ∷ y₂' ∷ y₃' ∷ [ y₄' ]) _ ps≡' refl) ps≡') (solve (++-monoid UInt8))
            in
            contradiction
              (success _ _ refl refl suffix (Lemmas.++-cancel≡ˡ _ _ (MonthDayHourMinSecFields.nonnesting (sym ps≡″) mmddhhmmss v₁) (sym ps≡″)))
              ¬parse
    case All.all? (inRange? '0' '9') v₀ of λ where
      (no ¬allv₀) → do
        tell $ here' String.++ ": bad year"
        return ∘ no $ λ where
          (success prefix@._ read read≡ (mkGenTimeFields year yearRange mmddhhmmss z≡ refl) suffix ps≡) →
            contradiction
              (subst (All (InRange '0' '9')) (proj₁ $ Lemmas.length-++-≡ _ _ _ _ (trans ps≡ (sym ps≡₀)) refl) yearRange)
              ¬allv₀
      (yes allv₀) →
        return (yes
          (success (v₀ ++ pre₁ ++ pre₂) (r₀ + r₁ + 1)
            (begin r₀ + r₁ + 1                       ≡⟨ cong (λ x → x + r₁ + 1) r₀≡ ⟩
                   length v₀ + r₁ + 1                ≡⟨ cong (λ x → length v₀ + x + 1) r₁≡ ⟩
                   length (v₀ ++ pre₁) + length pre₂ ≡⟨ sym $ length-++ (v₀ ++ pre₁) ⟩
                   length (v₀ ++ pre₁ ++ pre₂)       ∎)
            (mkGenTimeFields self allv₀ v₁ refl refl) suf₂
            (begin (v₀ ++ pre₁ ++ pre₂) ++ suf₂  ≡⟨ cong (v₀ ++_) (solve (++-monoid UInt8)) ⟩
                    v₀ ++ pre₁ ++ (pre₂ ++ suf₂) ≡⟨ cong (λ x → v₀ ++ pre₁ ++ x) ps≡₂ ⟩
                    v₀ ++ pre₁ ++ suf₁           ≡⟨ cong (v₀ ++_) ps≡₁ ⟩
                    v₀ ++ suf₀                   ≡⟨ ps≡₀ ⟩
                    xs                           ∎)))

open parseGenTimeFields public using (parseGenTimeFields)

parseGenTime : Parser (Logging ∘ Dec) GenTime
parseGenTime =
  parseTLV _ "GenTime" _
    (parseExactLength GenTime.nonnesting
      (tell $ "GenTime: length mismatch") parseGenTimeFields)

parseTime : Parser (Logging ∘ Dec) Time
runParser parseTime xs = do
  utc? ← runParser parseUTCTime xs
  case utc? of λ where
    (yes utc) → return (yes (mapSuccess (λ {bs} → utctm{bs}) utc))
    (no ¬utc) → do
      yes gen ← runParser parseGenTime xs
        where no ¬gen → do
          return ∘ no $ λ where
            (success prefix read read≡ (utctm x) suffix ps≡) →
              contradiction (success prefix _ read≡ x _ ps≡) ¬utc
            (success prefix read read≡ (gentm x) suffix ps≡) →
              contradiction (success prefix _ read≡ x _ ps≡) ¬gen
      return (yes (mapSuccess (λ {bs} → gentm{bs}) gen))



-- private
--   module Test where

--     Gen₁ : List Dig
--     Gen₁ = # Tag.GeneralizedTime ∷ # 15 ∷ # 50 ∷ # 56 ∷ # 52 ∷ # 49 ∷ # 48 ∷ # 54 ∷ # 50 ∷ # 52 ∷ # 49 ∷ # 56 ∷ # 51 ∷ # 54 ∷ # 53 ∷ # 52 ∷ [ # 90 ]

--     Utc₁ : List Dig
--     Utc₁ = # Tag.UTCTime ∷ # 13 ∷ # 57 ∷ # 55 ∷ # 48 ∷ # 53 ∷ # 51 ∷ # 48 ∷ # 49 ∷ # 52 ∷ # 52 ∷ # 56 ∷ # 50 ∷ # 50 ∷ [ # 90 ]

--     test₁ : Time Gen₁
--     test₁ = Success.value (toWitness {Q = Logging.val (runParser  parseTime Gen₁)} tt)

--     test₂ : Time Utc₁
--     test₂ = Success.value (toWitness {Q = Logging.val (runParser parseTime Utc₁)} tt)