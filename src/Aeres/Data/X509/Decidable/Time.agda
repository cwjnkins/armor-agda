{-# OPTIONS --subtyping --inversion-max-depth=100 #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Decidable.Length
open import Aeres.Data.X509.Decidable.TLV
open import Aeres.Data.X509.Properties
open import Aeres.Grammar.Definitions
open import Aeres.Grammar.Parser
open import Data.List.Properties
open import Data.Nat.Properties
  hiding (_≟_)
-- open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Decidable.Time where

open Base256

module parseMonthDayHourMinSecFields where
  here' = "parseMonthDayHourMinSecFields"

  parseMonthDayHourMinSecFields : Parser Dig (Logging ∘ Dec) Generic.MonthDayHourMinSecFields
  runParser parseMonthDayHourMinSecFields xs = do
    yes (success pre₀@._ ._ refl (mk×ₚ (singleton (mn1 ∷ mn2 ∷ d1 ∷ d2 ∷ h1 ∷ h2 ∷ mi1 ∷ mi2 ∷ s1 ∷ s2 ∷ []) refl) refl refl) suf₀ refl)
      ← runParser (parseN Dig (String.length "MMDDhhmmss") (tell $ here' String.++ ": underflow")) xs
      where no ¬parse → do
        return ∘ no $ λ where
          (success prefix@._ _ _ (Generic.mkMDHMSFields _ _ _ _ _ _ _ _ _ _ refl) suffix ps≡) →
            contradiction
              (success prefix _ refl (mk×ₚ singleSelf refl refl) suffix ps≡)
              ¬parse
    case check mn1 mn2 d1 d2 h1 h2 mi1 mi2 s1 s2 suf₀ of λ where
      (no  ¬check) → do
        tell $ here' String.++ ": range check failed"
        return (no ¬check)
      (yes ✓check) →
        return (yes ✓check)
    where
    check : ∀ mn1 mn2 d1 d2 h1 h2 mi1 mi2 s1 s2 suf₀
            → Dec (Success Dig Generic.MonthDayHourMinSecFields (mn1 ∷ mn2 ∷ d1 ∷ d2 ∷ h1 ∷ h2 ∷ mi1 ∷ mi2 ∷ s1 ∷ s2 ∷ suf₀))
    check mn1 mn2 d1 d2 h1 h2 mi1 mi2 s1 s2 suf₀
      with mn1 ≟ # 0 ×-dec inRange? '0' '9' mn2 ⊎-dec mn1 ≟ # 1 ×-dec inRange? '0' '2' mn2
    ... | no ¬mnᵣ = no λ where
      (success ._ ._ refl (Generic.mkMDHMSFields _ monRange _ _ _ _ _ _ _ _ refl) ._ refl) →
        contradiction monRange ¬mnᵣ
    ... | yes mnᵣ
      with inRange? '0' '2' d1 ×-dec inRange? '0' '9' d2 ⊎-dec toℕ d1 ≟ toℕ '3' ×-dec inRange? '0' '1' d2
    ... | no ¬dᵣ = no λ where
      (success ._ ._ refl (Generic.mkMDHMSFields _ _ _ dayRange _ _ _ _ _ _ refl) ._ refl) →
        contradiction dayRange ¬dᵣ
    ... | yes dᵣ
      with inRange? '0' '1' h1 ×-dec inRange? '0' '9' h2 ⊎-dec toℕ h1 ≟ toℕ '2' ×-dec inRange? '0' '3' h2
    ... | no ¬hᵣ = no λ where
      (success ._ ._ refl (Generic.mkMDHMSFields _ _ _ _ _ hourRange _ _ _ _ refl) ._ refl) →
        contradiction hourRange ¬hᵣ
    ... | yes hᵣ
      with inRange? '0' '5' mi1 ×-dec inRange? '0' '9' mi2
    ... | no ¬miᵣ = no λ where
      (success ._ ._ refl (Generic.mkMDHMSFields _ _ _ _ _ _ _ minRange _ _ refl) ._ refl) →
        contradiction minRange ¬miᵣ
    ... | yes miᵣ
      with inRange? '0' '5' s1 ×-dec inRange? '0' '9' s2
    ... | no ¬sᵣ = no λ where
      (success ._ ._ refl (Generic.mkMDHMSFields _ _ _ _ _ _ _ _ _ secRange refl) ._ refl) →
        contradiction secRange ¬sᵣ
    ... | yes sᵣ =
      yes (success _ _ refl
        (Generic.mkMDHMSFields singleSelf mnᵣ singleSelf dᵣ singleSelf hᵣ singleSelf miᵣ singleSelf sᵣ refl)
        suf₀ refl)

open parseMonthDayHourMinSecFields public using (parseMonthDayHourMinSecFields)

module parseUtcTimeFields where

  here' = "parseUtcTimeFields"
  open ≡-Reasoning

  parseUtcTimeFields : Parser Dig (Logging ∘ Dec) Generic.UtcTimeFields
  runParser parseUtcTimeFields xs = do
    yes (success ._ ._ refl (mk×ₚ (singleton (y₁ ∷ y₂ ∷ []) refl) refl refl) suf₀ refl)
      ← runParser (parseN Dig (String.length "YY") (tell $ here' String.++ ": underflow")) xs
      where no ¬parse → do
        return ∘ no $ λ where
          (success prefix@._ read read≡ (Generic.mkUtcTimeFields{y1 = y₁}{y₂} _ _ _ _ refl) suffix ps≡) →
            contradiction
              (success (y₁ ∷ [ y₂ ]) 2 refl (mk×ₚ singleSelf refl refl) _ ps≡)
              ¬parse
    yes (success pre₁@._ r₁ r₁≡ v₁@(Generic.mkMDHMSFields mon monᵣ day dayᵣ hour hourᵣ min minᵣ sec secᵣ refl) suf₁ ps≡₁)
      ← runParser parseMonthDayHourMinSecFields suf₀
      where no ¬parse → do
        tell $ here'
        return ∘ no $ λ where
          (success prefix read read≡ (Generic.mkUtcTimeFields{y1 = y₁'}{y₂'}{z = z} year yearRange mmddhhmmss term refl) suffix ps≡) → ‼
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
      ← runParser (parseLit Dig (tell $ here' String.++ ": underflow") (tell $ here' String.++ ": mismatch") [ # toℕ 'Z' ]) suf₁
      where no ¬parse → do
        return ∘ no $ λ where
          (success prefix@._ read read≡ (Generic.mkUtcTimeFields{y1 = y₁'}{y₂'}{z = z} year yearRange mmddhhmmss term refl) suffix ps≡) → ‼
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
          (success prefix read read≡ (Generic.mkUtcTimeFields{y1 = y₁'}{y₂'} year yearRange _ _ refl) suffix ps≡) →
            contradiction
              (subst (All (InRange '0' '9')) (proj₁ $ Lemmas.length-++-≡ _ _ _ _ ps≡ refl) yearRange)
              ¬yᵣ
      (yes yᵣ) →
        return (yes
          (success (y₁ ∷ y₂ ∷ pre₁ ++ [ # toℕ 'Z' ])
            (2 + r₁ + 1)
            (cong (2 +_) (begin r₁ + 1 ≡⟨ cong (_+ 1) r₁≡ ⟩
                                11     ∎))
            (Generic.mkUtcTimeFields singleSelf yᵣ v₁ refl refl)
            suf₂
            (cong (λ x → y₁ ∷ y₂ ∷ x) ps≡₁)))

