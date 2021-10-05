{-# OPTIONS --subtyping #-}

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

module parseUtcTimeFields where

  here' = "parseUtcTimeFields"

  parseUtcTimeFields : Parser Dig (Logging ∘ Dec) Generic.UtcTimeFields
  runParser parseUtcTimeFields xs = do
    yes (success pre₀@._ ._ refl (mk×ₚ (singleton (y1 ∷ y2 ∷ mn1 ∷ mn2 ∷ d1 ∷ d2 ∷ h1 ∷ h2 ∷ mi1 ∷ mi2 ∷ s1 ∷ s2 ∷ z ∷ []) refl) refl refl) suf₀ refl)
      ← runParser (parseN Dig (String.length "YYMMDD000000Z") (tell $ here' String.++ ": underflow")) xs
      where no ¬parse → do
        return ∘ no $ λ where
          (success _ _ _ (Generic.mkUtcTimeFields _ _ _ _ _ _ _ _ _ _ _ _ _ refl) suffix ps≡) →
            contradiction
              (success _ _ refl (mk×ₚ singleSelf refl refl) suffix ps≡)
              ¬parse
    case (check y1 y2 mn1 mn2 d1 d2 h1 h2 mi1 mi2 s1 s2 z suf₀) of λ where
      (no  ¬check)  → do
        tell $ here' String.++ ": bad time format"
        return (no ¬check)
      (yes checkOk) → return (yes checkOk)
    where
    check : ∀ y1 y2 mn1 mn2 d1 d2 h1 h2 mi1 mi2 s1 s2 z suf₀
            → Dec (Success Dig Generic.UtcTimeFields (y1 ∷ y2 ∷ mn1 ∷ mn2 ∷ d1 ∷ d2 ∷ h1 ∷ h2 ∷ mi1 ∷ mi2 ∷ s1 ∷ s2 ∷ z ∷ suf₀))
    check y1 y2 mn1 mn2 d1 d2 h1 h2 mi1 mi2 s1 s2 z suf₀
      with All.all? (inRange? '0' '9') (y1 ∷ [ y2 ])
    ... | no ¬yᵣ = no λ where
      (success prefix@._ read read≡ (Generic.mkUtcTimeFields _ yearRange _ _ _ _ _ _ _ _ _ _ _ refl) suffix refl) →
        contradiction yearRange ¬yᵣ
    ... | yes yᵣ
      with mn1 ≟ # 0 ×-dec inRange? '0' '9' mn2 ⊎-dec mn1 ≟ # 1 ×-dec inRange? '0' '2' mn2
    ... | no ¬mnᵣ = no λ where
      (success prefix@._ _ refl (Generic.mkUtcTimeFields _ _ _ monRange _ _ _ _ _ _ _ _ _ refl) suffix refl) →
        contradiction monRange ¬mnᵣ
    ... | yes mnᵣ
      with inRange? '0' '2' d1 ×-dec inRange? '0' '9' d2 ⊎-dec toℕ d1 ≟ toℕ '3' ×-dec inRange? '0' '1' d2
    ... | no ¬dᵣ = no λ where
      (success ._ ._ refl (Generic.mkUtcTimeFields _ _ _ _ _ dayRange _ _ _ _ _ _ _ refl) _ refl) →
        contradiction dayRange ¬dᵣ
    ... | yes dᵣ
      with inRange? '0' '1' h1 ×-dec inRange? '0' '9' h2 ⊎-dec toℕ h1 ≟ toℕ '2' ×-dec inRange? '0' '3' h2
    ... | no ¬hᵣ = no λ where
      (success ._ _ refl (Generic.mkUtcTimeFields _ _ _ _ _ _ _ hourRange _ _ _ _ _ refl) _ refl) →
        contradiction hourRange ¬hᵣ
    ... | yes hᵣ
      with inRange? '0' '5' mi1 ×-dec inRange? '0' '9' mi2
    ... | no ¬miᵣ = no λ where
      (success ._ ._ refl (Generic.mkUtcTimeFields _ _ _ _ _ _ _ _ _ minRange _ _ _ refl) _ refl) →
        contradiction minRange ¬miᵣ
    ... | yes miᵣ
      with inRange? '0' '5' s1 ×-dec inRange? '0' '9' s2
    ... | no ¬sᵣ = no λ where
      (success ._ ._ refl (Generic.mkUtcTimeFields _ _ _ _ _ _ _ _ _ _ _ secRange _ refl) _ refl) →
        contradiction secRange ¬sᵣ
    ... | yes sᵣ
      with toℕ z ≟ toℕ 'Z'
    ... | no  z≢ = no λ where
      (success ._ ._ refl (Generic.mkUtcTimeFields _ _ _ _ _ _ _ _ _ _ _ _ term refl) ._ refl) →
        contradiction term z≢
    ... | yes z≡ =
     yes (success _ _ refl (Generic.mkUtcTimeFields singleSelf yᵣ singleSelf mnᵣ singleSelf dᵣ singleSelf hᵣ singleSelf miᵣ singleSelf sᵣ z≡ refl ) suf₀ refl)


  parseUtcTime : Parser Dig (Logging ∘ Dec) Generic.UtcTime
  parseUtcTime =
    parseTLV Tag.Utctime "UTCTime" _
      (parseExactLength Dig NonNesting.UtcTimeFields (tell $ "parseUTCTime: length mistmatch") parseUtcTimeFields)
