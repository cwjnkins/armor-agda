{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Prelude
open import Data.Nat.Properties

module Aeres.Data.X509.Properties.Time.Ordering where

open Base256

module SemanticTime where
  record SemanticTime {@0 bs : List Dig} (t : Generic.Time bs) : Set where
    constructor mkSemanticTime
    field
      year  : Singleton (Generic.Time.getYear t)
      month : Singleton (Generic.Time.getMonth t)
      day   : Singleton (Generic.Time.getDay t)
      hour  : Singleton (Generic.Time.getHour t)
      min   : Singleton (Generic.Time.getMin t)
      sec   : Singleton (Generic.Time.getSec t)

  record Equiv {@0 bs₁ bs₂ : List Dig} {t₁ : Generic.Time bs₁} {t₂ : Generic.Time bs₂} (st₁ : SemanticTime t₁) (st₂ : SemanticTime t₂) : Set where
    constructor mkSemanticTimeEq
    field
      year≡  : Singleton.x (SemanticTime.year  st₁) ≡ Singleton.x (SemanticTime.year  st₂)
      month≡ : Singleton.x (SemanticTime.month st₁) ≡ Singleton.x (SemanticTime.month st₂)
      day≡   : Singleton.x (SemanticTime.day   st₁) ≡ Singleton.x (SemanticTime.day   st₂)
      hour≡  : Singleton.x (SemanticTime.hour  st₁) ≡ Singleton.x (SemanticTime.hour  st₂)
      min≡   : Singleton.x (SemanticTime.min   st₁) ≡ Singleton.x (SemanticTime.min   st₂)
      sec≡   : Singleton.x (SemanticTime.sec   st₁) ≡ Singleton.x (SemanticTime.sec   st₂)

  -- SemanticTimeEq is an equivalence relation
  reflexiveEquiv : ∀ {@0 bs} {t : Generic.Time bs} → (st : SemanticTime t) → Equiv st st
  Equiv.year≡ (reflexiveEquiv st) = refl
  Equiv.month≡ (reflexiveEquiv st) = refl
  Equiv.day≡ (reflexiveEquiv st) = refl
  Equiv.hour≡ (reflexiveEquiv st) = refl
  Equiv.min≡ (reflexiveEquiv st) = refl
  Equiv.sec≡ (reflexiveEquiv st) = refl


  symmetricEquiv : ∀ {@0 bs₁ bs₂} {t₁ : Generic.Time bs₁} {t₂ : Generic.Time bs₂} → (st₁ : SemanticTime t₁) (st₂ : SemanticTime t₂) → Equiv st₁ st₂ → Equiv st₂ st₁
  Equiv.year≡ (symmetricEquiv st₁ st₂ eq) = sym (Equiv.year≡ eq)
  Equiv.month≡ (symmetricEquiv st₁ st₂ eq) = sym (Equiv.month≡ eq)
  Equiv.day≡ (symmetricEquiv st₁ st₂ eq) = sym (Equiv.day≡ eq)
  Equiv.hour≡ (symmetricEquiv st₁ st₂ eq) = sym (Equiv.hour≡ eq)
  Equiv.min≡ (symmetricEquiv st₁ st₂ eq) = sym (Equiv.min≡ eq)
  Equiv.sec≡ (symmetricEquiv st₁ st₂ eq) = sym (Equiv.sec≡ eq)

  transitiveEquiv : ∀ {@0 bs₁ bs₂ bs₃} {t₁ : Generic.Time bs₁} {t₂ : Generic.Time bs₂} {t₃ : Generic.Time bs₃}
               → (st₁ : SemanticTime t₁) (st₂ : SemanticTime t₂) (st₃ : SemanticTime t₃)
               → Equiv st₁ st₂ → Equiv st₂ st₃ → Equiv st₁ st₃
  Equiv.year≡ (transitiveEquiv st₁ st₂ st₃ eq₁₂ eq₂₃) = trans (Equiv.year≡ eq₁₂) (Equiv.year≡ eq₂₃)
  Equiv.month≡ (transitiveEquiv st₁ st₂ st₃ eq₁₂ eq₂₃) = trans (Equiv.month≡ eq₁₂) (Equiv.month≡ eq₂₃)
  Equiv.day≡ (transitiveEquiv st₁ st₂ st₃ eq₁₂ eq₂₃) = trans (Equiv.day≡ eq₁₂) (Equiv.day≡ eq₂₃)
  Equiv.hour≡ (transitiveEquiv st₁ st₂ st₃ eq₁₂ eq₂₃) = trans (Equiv.hour≡ eq₁₂) (Equiv.hour≡ eq₂₃)
  Equiv.min≡ (transitiveEquiv st₁ st₂ st₃ eq₁₂ eq₂₃) = trans (Equiv.min≡ eq₁₂) (Equiv.min≡ eq₂₃)
  Equiv.sec≡ (transitiveEquiv st₁ st₂ st₃ eq₁₂ eq₂₃) = trans (Equiv.sec≡ eq₁₂) (Equiv.sec≡ eq₂₃)

  data LE {@0 bs₁ bs₂ : List Dig} {t₁ : Generic.Time bs₁} {t₂ : Generic.Time bs₂} (st₁ : SemanticTime t₁) (st₂ : SemanticTime t₂) : Set where
    year<  : Singleton.x (SemanticTime.year st₁) < Singleton.x (SemanticTime.year st₂) → LE st₁ st₂
    month< : Singleton.x (SemanticTime.year st₁) ≡ Singleton.x (SemanticTime.year st₂)
             → Singleton.x (SemanticTime.month st₁) < Singleton.x (SemanticTime.month st₂) → LE st₁ st₂
    day<   : Singleton.x (SemanticTime.year st₁) ≡ Singleton.x (SemanticTime.year st₂)
             → Singleton.x (SemanticTime.month st₁) ≡ Singleton.x (SemanticTime.month st₂)
             → Singleton.x (SemanticTime.day st₁) < Singleton.x (SemanticTime.day st₂) → LE st₁ st₂
    hour<  : Singleton.x (SemanticTime.year st₁) ≡ Singleton.x (SemanticTime.year st₂)
             → Singleton.x (SemanticTime.month st₁) ≡ Singleton.x (SemanticTime.month st₂)
             → Singleton.x (SemanticTime.day st₁) ≡ Singleton.x (SemanticTime.day st₂)
             → Singleton.x (SemanticTime.hour st₁) < Singleton.x (SemanticTime.hour st₂) → LE st₁ st₂
    min<   : Singleton.x (SemanticTime.year st₁) ≡ Singleton.x (SemanticTime.year st₂)
             → Singleton.x (SemanticTime.month st₁) ≡ Singleton.x (SemanticTime.month st₂)
             → Singleton.x (SemanticTime.day st₁) ≡ Singleton.x (SemanticTime.day st₂)
             → Singleton.x (SemanticTime.hour st₁) ≡ Singleton.x (SemanticTime.hour st₂)
             → Singleton.x (SemanticTime.min st₁) < Singleton.x (SemanticTime.min st₂)
             → LE st₁ st₂
    sec<   : Singleton.x (SemanticTime.year st₁) ≡ Singleton.x (SemanticTime.year st₂)
             → Singleton.x (SemanticTime.month st₁) ≡ Singleton.x (SemanticTime.month st₂)
             → Singleton.x (SemanticTime.day st₁) ≡ Singleton.x (SemanticTime.day st₂)
             → Singleton.x (SemanticTime.hour st₁) ≡ Singleton.x (SemanticTime.hour st₂)
             → Singleton.x (SemanticTime.min st₁) ≡ Singleton.x (SemanticTime.min st₂)
             → Singleton.x (SemanticTime.sec st₁) < Singleton.x (SemanticTime.sec st₂)
             → LE st₁ st₂
    eq    : Equiv st₁ st₂ → LE st₁ st₂

  module _ {@0 bs₁ bs₂} {t₁ : Generic.Time bs₁} {t₂ : Generic.Time bs₂} {st₁ : SemanticTime t₁} {st₂ : SemanticTime t₂} where
    yearLE : LE st₁ st₂ → Singleton.x (SemanticTime.year st₁) ≤ Singleton.x (SemanticTime.year st₂)
    yearLE (year< x) = <⇒≤ x
    yearLE (month< x x₁) = Lemmas.≡⇒≤ x
    yearLE (day< x x₁ x₂) = Lemmas.≡⇒≤ x
    yearLE (hour< x x₁ x₂ x₃) = Lemmas.≡⇒≤ x
    yearLE (min< x x₁ x₂ x₃ x₄) = Lemmas.≡⇒≤ x
    yearLE (sec< x x₁ x₂ x₃ x₄ x₅) = Lemmas.≡⇒≤ x
    yearLE (eq x) = Lemmas.≡⇒≤ (Equiv.year≡ x)

    monthLE : LE st₁ st₂
              → Singleton.x (SemanticTime.year st₁)  ≡ Singleton.x (SemanticTime.year st₂)
              → Singleton.x (SemanticTime.month st₁) ≤ Singleton.x (SemanticTime.month st₂)
    monthLE (year< x)                refl = contradiction refl (<⇒≢ x)
    monthLE (month< x x₁)            refl = <⇒≤ x₁
    monthLE (day< x x₁ x₂)           refl = Lemmas.≡⇒≤ x₁
    monthLE (hour< x x₁ x₂ x₃)       refl = Lemmas.≡⇒≤ x₁
    monthLE (min< x x₁ x₂ x₃ x₄)     refl = Lemmas.≡⇒≤ x₁
    monthLE (sec< x x₁ x₂ x₃ x₄ x₅)  refl = Lemmas.≡⇒≤ x₁
    monthLE (eq x)                   refl = Lemmas.≡⇒≤ (Equiv.month≡ x)

    dayLE : LE st₁ st₂
            → Singleton.x (SemanticTime.year st₁)  ≡ Singleton.x (SemanticTime.year st₂)
            → Singleton.x (SemanticTime.month st₁)  ≡ Singleton.x (SemanticTime.month st₂)
            → Singleton.x (SemanticTime.day st₁) ≤ Singleton.x (SemanticTime.day st₂)
    dayLE (year< x)                refl refl = contradiction refl (<⇒≢ x)
    dayLE (month< x x₁)            refl refl = contradiction refl (<⇒≢ x₁)
    dayLE (day< x x₁ x₂)           refl refl = <⇒≤ x₂
    dayLE (hour< x x₁ x₂ x₃)       refl refl = Lemmas.≡⇒≤ x₂
    dayLE (min< x x₁ x₂ x₃ x₄)     refl refl = Lemmas.≡⇒≤ x₂
    dayLE (sec< x x₁ x₂ x₃ x₄ x₅)  refl refl = Lemmas.≡⇒≤ x₂
    dayLE (eq x)                   refl refl = Lemmas.≡⇒≤ (Equiv.day≡ x)

    hourLE : LE st₁ st₂
            → Singleton.x (SemanticTime.year st₁)  ≡ Singleton.x (SemanticTime.year st₂)
            → Singleton.x (SemanticTime.month st₁)  ≡ Singleton.x (SemanticTime.month st₂)
            → Singleton.x (SemanticTime.day st₁) ≡ Singleton.x (SemanticTime.day st₂)
            → Singleton.x (SemanticTime.hour st₁) ≤ Singleton.x (SemanticTime.hour st₂)
    hourLE (year< x)                refl refl refl = contradiction refl (<⇒≢ x)
    hourLE (month< x x₁)            refl refl refl = contradiction refl (<⇒≢ x₁)
    hourLE (day< x x₁ x₂)           refl refl refl = contradiction refl (<⇒≢ x₂)
    hourLE (hour< x x₁ x₂ x₃)       refl refl refl = <⇒≤ x₃
    hourLE (min< x x₁ x₂ x₃ x₄)     refl refl refl = Lemmas.≡⇒≤ x₃
    hourLE (sec< x x₁ x₂ x₃ x₄ x₅)  refl refl refl = Lemmas.≡⇒≤ x₃
    hourLE (eq x)                   refl refl refl = Lemmas.≡⇒≤ (Equiv.hour≡ x)

    minLE : LE st₁ st₂
            → Singleton.x (SemanticTime.year st₁)  ≡ Singleton.x (SemanticTime.year st₂)
            → Singleton.x (SemanticTime.month st₁)  ≡ Singleton.x (SemanticTime.month st₂)
            → Singleton.x (SemanticTime.day st₁) ≡ Singleton.x (SemanticTime.day st₂)
            → Singleton.x (SemanticTime.hour st₁) ≡ Singleton.x (SemanticTime.hour st₂)
            → Singleton.x (SemanticTime.min st₁) ≤ Singleton.x (SemanticTime.min st₂)
    minLE (year< x)                refl refl refl refl = contradiction refl (<⇒≢ x)
    minLE (month< x x₁)            refl refl refl refl = contradiction refl (<⇒≢ x₁)
    minLE (day< x x₁ x₂)           refl refl refl refl = contradiction refl (<⇒≢ x₂)
    minLE (hour< x x₁ x₂ x₃)       refl refl refl refl = contradiction refl (<⇒≢ x₃)
    minLE (min< x x₁ x₂ x₃ x₄)     refl refl refl refl =  <⇒≤ x₄
    minLE (sec< x x₁ x₂ x₃ x₄ x₅)  refl refl refl refl = Lemmas.≡⇒≤ x₄
    minLE (eq x)                   refl refl refl refl = Lemmas.≡⇒≤ (Equiv.min≡ x)

    secLE : LE st₁ st₂
            → Singleton.x (SemanticTime.year st₁)  ≡ Singleton.x (SemanticTime.year st₂)
            → Singleton.x (SemanticTime.month st₁)  ≡ Singleton.x (SemanticTime.month st₂)
            → Singleton.x (SemanticTime.day st₁) ≡ Singleton.x (SemanticTime.day st₂)
            → Singleton.x (SemanticTime.hour st₁) ≡ Singleton.x (SemanticTime.hour st₂)
            → Singleton.x (SemanticTime.min st₁) ≡ Singleton.x (SemanticTime.min st₂)
            → Singleton.x (SemanticTime.sec st₁) ≤ Singleton.x (SemanticTime.sec st₂)
    secLE (year< x)                refl refl refl refl refl = contradiction refl (<⇒≢ x)
    secLE (month< x x₁)            refl refl refl refl refl = contradiction refl (<⇒≢ x₁)
    secLE (day< x x₁ x₂)           refl refl refl refl refl = contradiction refl (<⇒≢ x₂)
    secLE (hour< x x₁ x₂ x₃)       refl refl refl refl refl = contradiction refl (<⇒≢ x₃)
    secLE (min< x x₁ x₂ x₃ x₄)     refl refl refl refl refl = contradiction refl (<⇒≢ x₄)
    secLE (sec< x x₁ x₂ x₃ x₄ x₅)  refl refl refl refl refl = <⇒≤ x₅
    secLE (eq x)                   refl refl refl refl refl = Lemmas.≡⇒≤ (Equiv.sec≡ x)



  reflexiveLE :  ∀ {@0 bs} {t : Generic.Time bs} → (st : SemanticTime t) → LE st st
  reflexiveLE st = LE.eq (reflexiveEquiv st)

  transitiveLE
    : ∀ {@0 bs₁ bs₂ bs₃} {t₁ : Generic.Time bs₁} {t₂ : Generic.Time bs₂} {t₃ : Generic.Time bs₃}
      → (st₁ : SemanticTime t₁) (st₂ : SemanticTime t₂) (st₃ : SemanticTime t₃)
      → LE st₁ st₂ → LE st₂ st₃ → LE st₁ st₃
  transitiveLE st₁ st₂ st₃ (year< x) (year< x₁) = year< (<-trans x x₁)
  transitiveLE st₁ st₂ st₃ (year< x) (month< x₁ x₂) = year< (≤-trans x (Lemmas.≡⇒≤ x₁))
  transitiveLE st₁ st₂ st₃ (year< x) (day< x₁ x₂ x₃) = year< (≤-trans x (Lemmas.≡⇒≤ x₁))
  transitiveLE st₁ st₂ st₃ (year< x) (hour< x₁ x₂ x₃ x₄) = year< (≤-trans x (Lemmas.≡⇒≤ x₁))
  transitiveLE st₁ st₂ st₃ (year< x) (min< x₁ x₂ x₃ x₄ x₅) = year< (≤-trans x (Lemmas.≡⇒≤ x₁))
  transitiveLE st₁ st₂ st₃ (year< x) (sec< x₁ x₂ x₃ x₄ x₅ x₆) = year< (≤-trans x (Lemmas.≡⇒≤ x₁))
  transitiveLE st₁ st₂ st₃ (year< x) (eq x₁) = year< (≤-trans x (Lemmas.≡⇒≤ (Equiv.year≡ x₁)))
  transitiveLE st₁ st₂ st₃ (month< x x₁) (year< x₂) = year< (≤-trans (Lemmas.≡⇒≤ (cong suc x)) x₂)
  transitiveLE st₁ st₂ st₃ (month< x x₁) (month< x₂ x₃) = month< (trans x x₂) (<-trans x₁ x₃)
  transitiveLE st₁ st₂ st₃ (month< x x₁) (day< x₂ x₃ x₄) = month< (trans x x₂) (≤-trans x₁ (Lemmas.≡⇒≤ x₃))
  transitiveLE st₁ st₂ st₃ (month< x x₁) (hour< x₂ x₃ x₄ x₅) = month< (trans x x₂) (≤-trans x₁ (Lemmas.≡⇒≤ x₃))
  transitiveLE st₁ st₂ st₃ (month< x x₁) (min< x₂ x₃ x₄ x₅ x₆) = month< (trans x x₂) (≤-trans x₁ (Lemmas.≡⇒≤ x₃))
  transitiveLE st₁ st₂ st₃ (month< x x₁) (sec< x₂ x₃ x₄ x₅ x₆ x₇) = month< (trans x x₂) (≤-trans x₁ (Lemmas.≡⇒≤ x₃))
  transitiveLE st₁ st₂ st₃ (month< x x₁) (eq x₂) = month< (trans x (Equiv.year≡ x₂)) (≤-trans x₁ (Lemmas.≡⇒≤ (Equiv.month≡ x₂)))
  transitiveLE st₁ st₂ st₃ (day< x x₁ x₂) (year< x₃) = year< (≤-trans (Lemmas.≡⇒≤ (cong suc x)) x₃)
  transitiveLE st₁ st₂ st₃ (day< x x₁ x₂) (month< x₃ x₄) = month< (trans x x₃) (≤-trans (Lemmas.≡⇒≤ (cong suc x₁)) x₄)
  transitiveLE st₁ st₂ st₃ (day< x x₁ x₂) (day< x₃ x₄ x₅) =
    day< (trans x x₃) (trans x₁ x₄) (<-trans x₂ x₅)
  transitiveLE st₁ st₂ st₃ (day< x x₁ x₂) (hour< x₃ x₄ x₅ x₆) =
    day< (trans x x₃) (trans x₁ x₄) (≤-trans x₂ (Lemmas.≡⇒≤ x₅))
  transitiveLE st₁ st₂ st₃ (day< x x₁ x₂) (min< x₃ x₄ x₅ x₆ x₇) =
    day< (trans x x₃) (trans x₁ x₄) (≤-trans x₂ (Lemmas.≡⇒≤ x₅))
  transitiveLE st₁ st₂ st₃ (day< x x₁ x₂) (sec< x₃ x₄ x₅ x₆ x₇ x₈) =
    day< (trans x x₃) (trans x₁ x₄) (≤-trans x₂ (Lemmas.≡⇒≤ x₅))
  transitiveLE st₁ st₂ st₃ (day< x x₁ x₂) (eq x₃) =
        day< (trans x (Equiv.year≡ x₃)) (trans x₁ (Equiv.month≡ x₃)) (≤-trans x₂ (Lemmas.≡⇒≤ (Equiv.day≡ x₃)))
  transitiveLE st₁ st₂ st₃ (hour< x x₁ x₂ x₃) (year< x₄) = year< (≤-trans (Lemmas.≡⇒≤ (cong suc x)) x₄)
  transitiveLE st₁ st₂ st₃ (hour< x x₁ x₂ x₃) (month< x₄ x₅) = month< (trans x x₄) (≤-trans (Lemmas.≡⇒≤ (cong suc x₁)) x₅)
  transitiveLE st₁ st₂ st₃ (hour< x x₁ x₂ x₃) (day< x₄ x₅ x₆)
    = day< (trans x x₄) (trans x₁ x₅) (≤-trans (Lemmas.≡⇒≤ (cong suc x₂)) x₆)
  transitiveLE st₁ st₂ st₃ (hour< x x₁ x₂ x₃) (hour< x₄ x₅ x₆ x₇) =
    hour< (trans x x₄) (trans x₁ x₅) (trans x₂ x₆) (<-trans x₃ x₇)
  transitiveLE st₁ st₂ st₃ (hour< x x₁ x₂ x₃) (min< x₄ x₅ x₆ x₇ x₈) =
    hour< (trans x x₄) (trans x₁ x₅) (trans x₂ x₆) (≤-trans x₃ (Lemmas.≡⇒≤ x₇))
  transitiveLE st₁ st₂ st₃ (hour< x x₁ x₂ x₃) (sec< x₄ x₅ x₆ x₇ x₈ x₉) =
    hour< (trans x x₄) (trans x₁ x₅) (trans x₂ x₆) (≤-trans x₃ (Lemmas.≡⇒≤ x₇))
  transitiveLE st₁ st₂ st₃ (hour< x x₁ x₂ x₃) (eq x₄) =
    hour< (trans x (Equiv.year≡ x₄)) (trans x₁ (Equiv.month≡ x₄)) (trans x₂ (Equiv.day≡ x₄)) (≤-trans x₃ (Lemmas.≡⇒≤ (Equiv.hour≡ x₄)))
  transitiveLE st₁ st₂ st₃ (min< x x₁ x₂ x₃ x₄) (year< x₅) = year< (≤-trans (Lemmas.≡⇒≤ (cong suc x)) x₅)
  transitiveLE st₁ st₂ st₃ (min< x x₁ x₂ x₃ x₄) (month< x₅ x₆) = month< (trans x x₅) (≤-trans (Lemmas.≡⇒≤ (cong suc x₁)) x₆)
  transitiveLE st₁ st₂ st₃ (min< x x₁ x₂ x₃ x₄) (day< x₅ x₆ x₇) =
    day< (trans x x₅) (trans x₁ x₆) (≤-trans (Lemmas.≡⇒≤ (cong suc x₂)) x₇)
  transitiveLE st₁ st₂ st₃ (min< x x₁ x₂ x₃ x₄) (hour< x₅ x₆ x₇ x₈) =
    hour< (trans x x₅) (trans x₁ x₆) (trans x₂ x₇) (≤-trans (Lemmas.≡⇒≤ (cong suc x₃)) x₈)
  transitiveLE st₁ st₂ st₃ (min< x x₁ x₂ x₃ x₄) (min< x₅ x₆ x₇ x₈ x₉) =
    min< (trans x x₅) (trans x₁ x₆) (trans x₂ x₇) (trans x₃ x₈) (<-trans x₄ x₉)
  transitiveLE st₁ st₂ st₃ (min< x x₁ x₂ x₃ x₄) (sec< x₅ x₆ x₇ x₈ x₉ x₁₀) =
    min< (trans x x₅) (trans x₁ x₆) (trans x₂ x₇) (trans x₃ x₈) (≤-trans x₄ (Lemmas.≡⇒≤ x₉))
  transitiveLE st₁ st₂ st₃ (min< x x₁ x₂ x₃ x₄) (eq x₅) =
     min< (trans x (Equiv.year≡ x₅)) (trans x₁ (Equiv.month≡ x₅)) (trans x₂ (Equiv.day≡ x₅)) (trans x₃ (Equiv.hour≡ x₅)) (≤-trans x₄ (Lemmas.≡⇒≤ (Equiv.min≡ x₅)))
  transitiveLE st₁ st₂ st₃ (sec< x x₁ x₂ x₃ x₄ x₅) (year< x₆) = year< (≤-trans (Lemmas.≡⇒≤ (cong suc x)) x₆)
  transitiveLE st₁ st₂ st₃ (sec< x x₁ x₂ x₃ x₄ x₅) (month< x₆ x₇) = month< (trans x x₆) (≤-trans (Lemmas.≡⇒≤ (cong suc x₁)) x₇)
  transitiveLE st₁ st₂ st₃ (sec< x x₁ x₂ x₃ x₄ x₅) (day< x₆ x₇ x₈) =
    day< (trans x x₆) (trans x₁ x₇) (≤-trans (Lemmas.≡⇒≤ (cong suc x₂)) x₈)
  transitiveLE st₁ st₂ st₃ (sec< x x₁ x₂ x₃ x₄ x₅) (hour< x₆ x₇ x₈ x₉) =
    hour< (trans x x₆) (trans x₁ x₇) (trans x₂ x₈) (≤-trans (Lemmas.≡⇒≤ (cong suc x₃)) x₉)
  transitiveLE st₁ st₂ st₃ (sec< x x₁ x₂ x₃ x₄ x₅) (min< x₆ x₇ x₈ x₉ x₁₀) =
    min< (trans x x₆) (trans x₁ x₇) (trans x₂ x₈) (trans x₃ x₉) (≤-trans (Lemmas.≡⇒≤ (cong suc x₄)) x₁₀)
  transitiveLE st₁ st₂ st₃ (sec< x x₁ x₂ x₃ x₄ x₅) (sec< x₆ x₇ x₈ x₉ x₁₀ x₁₁) =
    sec< (trans x x₆) (trans x₁ x₇) (trans x₂ x₈) (trans x₃ x₉) (trans x₄ x₁₀) (<-trans x₅ x₁₁)
  transitiveLE st₁ st₂ st₃ (sec< x x₁ x₂ x₃ x₄ x₅) (eq x₆) =
    sec< (trans x (Equiv.year≡ x₆)) (trans x₁ (Equiv.month≡ x₆)) (trans x₂ (Equiv.day≡ x₆)) (trans x₃ (Equiv.hour≡ x₆)) (trans x₄ (Equiv.min≡ x₆)) (≤-trans x₅ (Lemmas.≡⇒≤ (Equiv.sec≡ x₆)))
  transitiveLE st₁ st₂ st₃ (eq x) (year< x₁) = year< (≤-trans (Lemmas.≡⇒≤ (cong suc (Equiv.year≡ x))) x₁)
  transitiveLE st₁ st₂ st₃ (eq x) (month< x₁ x₂) = month< (trans (Equiv.year≡ x) x₁) (≤-trans (Lemmas.≡⇒≤ (cong suc (Equiv.month≡ x))) x₂)
  transitiveLE st₁ st₂ st₃ (eq x) (day< x₁ x₂ x₃) =
    day< (trans (Equiv.year≡ x) x₁) (trans (Equiv.month≡ x) x₂) (≤-trans (Lemmas.≡⇒≤ (cong suc (Equiv.day≡ x))) x₃)
  transitiveLE st₁ st₂ st₃ (eq x) (hour< x₁ x₂ x₃ x₄) =
    hour< (trans (Equiv.year≡ x) x₁) (trans (Equiv.month≡ x) x₂) (trans (Equiv.day≡ x) x₃) (≤-trans (Lemmas.≡⇒≤ (cong suc (Equiv.hour≡ x))) x₄)
  transitiveLE st₁ st₂ st₃ (eq x) (min< x₁ x₂ x₃ x₄ x₅) =
    min< (trans (Equiv.year≡ x) x₁) (trans (Equiv.month≡ x) x₂) (trans (Equiv.day≡ x) x₃) (trans (Equiv.hour≡ x) x₄) (≤-trans (Lemmas.≡⇒≤ (cong suc (Equiv.min≡ x))) x₅)
  transitiveLE st₁ st₂ st₃ (eq x) (sec< x₁ x₂ x₃ x₄ x₅ x₆) =
    sec< (trans (Equiv.year≡ x) x₁) (trans (Equiv.month≡ x) x₂) (trans (Equiv.day≡ x) x₃) (trans (Equiv.hour≡ x) x₄) (trans (Equiv.min≡ x) x₅)  (≤-trans (Lemmas.≡⇒≤ (cong suc (Equiv.sec≡ x))) x₆)
  transitiveLE st₁ st₂ st₃ (eq x) (eq x₁) = eq (transitiveEquiv _ _ _ x x₁)

  antiSymLE
    : ∀ {@0 bs₁ bs₂ bs₃} {t₁ : Generic.Time bs₁} {t₂ : Generic.Time bs₂} {t₃ : Generic.Time bs₃}
      → (st₁ : SemanticTime t₁) (st₂ : SemanticTime t₂)
      → LE st₁ st₂ → LE st₂ st₁ → Equiv st₁ st₂
  antiSymLE st₁ st₂ (year< x) (year< x₁) =
    contradiction x (<⇒≯ x₁)
  antiSymLE st₁ st₂ (year< x) (month< x₁ x₂) =
    contradiction (sym x₁) (<⇒≢ x)
  antiSymLE st₁ st₂ (year< x) (day< x₁ x₂ x₃) =
    contradiction (sym x₁) (<⇒≢ x)
  antiSymLE st₁ st₂ (year< x) (hour< x₁ x₂ x₃ x₄) =
    contradiction (sym x₁) (<⇒≢ x)
  antiSymLE st₁ st₂ (year< x) (min< x₁ x₂ x₃ x₄ x₅) =
    contradiction (sym x₁) (<⇒≢ x)
  antiSymLE st₁ st₂ (year< x) (sec< x₁ x₂ x₃ x₄ x₅ x₆) =
    contradiction (sym x₁) (<⇒≢ x)
  antiSymLE st₁ st₂ (year< x) (eq x₁) = symmetricEquiv _ _ x₁
  antiSymLE st₁ st₂ (month< x x₁) (year< x₂) =
    contradiction (sym x) (<⇒≢ x₂)
  antiSymLE st₁ st₂ (month< x x₁) (month< x₂ x₃) =
    contradiction x₁ (<⇒≯ x₃)
  antiSymLE st₁ st₂ (month< x x₁) (day< x₂ x₃ x₄) =
    contradiction (sym x₃) (<⇒≢ x₁)
  antiSymLE st₁ st₂ (month< x x₁) (hour< x₂ x₃ x₄ x₅) =
    contradiction (sym x₃) (<⇒≢ x₁)
  antiSymLE st₁ st₂ (month< x x₁) (min< x₂ x₃ x₄ x₅ x₆) =
    contradiction (sym x₃) (<⇒≢ x₁)
  antiSymLE st₁ st₂ (month< x x₁) (sec< x₂ x₃ x₄ x₅ x₆ x₇) =
    contradiction (sym x₃) (<⇒≢ x₁)
  antiSymLE st₁ st₂ (month< x x₁) (eq x₂) = symmetricEquiv _ _ x₂
  antiSymLE st₁ st₂ (day< x x₁ x₂) (year< x₃) =
    contradiction (sym x) (<⇒≢ x₃)
  antiSymLE st₁ st₂ (day< x x₁ x₂) (month< x₃ x₄) =
    contradiction (sym x₁) (<⇒≢ x₄)
  antiSymLE st₁ st₂ (day< x x₁ x₂) (day< x₃ x₄ x₅) =
    contradiction x₂ (<⇒≯ x₅)
  antiSymLE st₁ st₂ (day< x x₁ x₂) (hour< x₃ x₄ x₅ x₆) =
    contradiction (sym x₅) (<⇒≢ x₂)
  antiSymLE st₁ st₂ (day< x x₁ x₂) (min< x₃ x₄ x₅ x₆ x₇) =
    contradiction (sym x₅) (<⇒≢ x₂)
  antiSymLE st₁ st₂ (day< x x₁ x₂) (sec< x₃ x₄ x₅ x₆ x₇ x₈) =
    contradiction (sym x₅) (<⇒≢ x₂)
  antiSymLE st₁ st₂ (day< x x₁ x₂) (eq x₃) = symmetricEquiv _ _ x₃
  antiSymLE st₁ st₂ (hour< x x₁ x₂ x₃) (year< x₄) =
    contradiction (sym x) (<⇒≢ x₄)
  antiSymLE st₁ st₂ (hour< x x₁ x₂ x₃) (month< x₄ x₅) =
    contradiction (sym x₁) (<⇒≢ x₅)
  antiSymLE st₁ st₂ (hour< x x₁ x₂ x₃) (day< x₄ x₅ x₆) =
    contradiction (sym x₂) (<⇒≢ x₆)
  antiSymLE st₁ st₂ (hour< x x₁ x₂ x₃) (hour< x₄ x₅ x₆ x₇) =
    contradiction x₃ (<⇒≯ x₇)
  antiSymLE st₁ st₂ (hour< x x₁ x₂ x₃) (min< x₄ x₅ x₆ x₇ x₈) =
    contradiction (sym x₇) (<⇒≢ x₃)
  antiSymLE st₁ st₂ (hour< x x₁ x₂ x₃) (sec< x₄ x₅ x₆ x₇ x₈ x₉) =
    contradiction (sym x₇) (<⇒≢ x₃)
  antiSymLE st₁ st₂ (hour< x x₁ x₂ x₃) (eq x₄) = symmetricEquiv _ _ x₄
  antiSymLE st₁ st₂ (min< x x₁ x₂ x₃ x₄) (year< x₅) =
    contradiction (sym x) (<⇒≢ x₅)
  antiSymLE st₁ st₂ (min< x x₁ x₂ x₃ x₄) (month< x₅ x₆) =
    contradiction (sym x₁) (<⇒≢ x₆)
  antiSymLE st₁ st₂ (min< x x₁ x₂ x₃ x₄) (day< x₅ x₆ x₇) =
    contradiction (sym x₂) (<⇒≢ x₇)
  antiSymLE st₁ st₂ (min< x x₁ x₂ x₃ x₄) (hour< x₅ x₆ x₇ x₈) =
    contradiction (sym x₃) (<⇒≢ x₈)
  antiSymLE st₁ st₂ (min< x x₁ x₂ x₃ x₄) (min< x₅ x₆ x₇ x₈ x₉) =
    contradiction x₄ (<⇒≯ x₉)
  antiSymLE st₁ st₂ (min< x x₁ x₂ x₃ x₄) (sec< x₅ x₆ x₇ x₈ x₉ x₁₀) =
    contradiction (sym x₉) (<⇒≢ x₄)
  antiSymLE st₁ st₂ (min< x x₁ x₂ x₃ x₄) (eq x₅) =
    symmetricEquiv _ _ x₅
  antiSymLE st₁ st₂ (sec< x x₁ x₂ x₃ x₄ x₅) (year< x₆) =
    contradiction (sym x) (<⇒≢ x₆)
  antiSymLE st₁ st₂ (sec< x x₁ x₂ x₃ x₄ x₅) (month< x₆ x₇) =
    contradiction (sym x₁) (<⇒≢ x₇)
  antiSymLE st₁ st₂ (sec< x x₁ x₂ x₃ x₄ x₅) (day< x₆ x₇ x₈) =
    contradiction (sym x₂) (<⇒≢ x₈)
  antiSymLE st₁ st₂ (sec< x x₁ x₂ x₃ x₄ x₅) (hour< x₆ x₇ x₈ x₉) =
    contradiction (sym x₃) (<⇒≢ x₉)
  antiSymLE st₁ st₂ (sec< x x₁ x₂ x₃ x₄ x₅) (min< x₆ x₇ x₈ x₉ x₁₀) =
    contradiction (sym x₄) (<⇒≢ x₁₀)
  antiSymLE st₁ st₂ (sec< x x₁ x₂ x₃ x₄ x₅) (sec< x₆ x₇ x₈ x₉ x₁₀ x₁₁) =
    contradiction x₅ (<⇒≯ x₁₁)
  antiSymLE st₁ st₂ (sec< x x₁ x₂ x₃ x₄ x₅) (eq x₆) = symmetricEquiv _ _ x₆
  antiSymLE st₁ st₂ (eq x) _ = x

  decidable
   : ∀ {@0 bs₁ bs₂ bs₃} {t₁ : Generic.Time bs₁} {t₂ : Generic.Time bs₂} {t₃ : Generic.Time bs₃}
     → (st₁ : SemanticTime t₁) (st₂ : SemanticTime t₂)
     → Dec (LE st₁ st₂)
  decidable st₁ st₂
    with <-cmp (Singleton.x $ SemanticTime.year st₁) (Singleton.x $ SemanticTime.year st₂)
  ... | tri< a ¬b ¬c = yes (year< a)
  ... | tri> ¬a ¬b c = no λ where
    x → contradiction (≤∧≢⇒< (yearLE x) ¬b) ¬a
  ... | tri≈ _ refl _
    with <-cmp (Singleton.x $ SemanticTime.month st₁) (Singleton.x $ SemanticTime.month st₂)
  ... | tri< a ¬b ¬c = yes (month< refl a)
  ... | tri> ¬a ¬b c = no λ x →
    contradiction (≤∧≢⇒< (monthLE x refl) ¬b) ¬a
  ... | tri≈ _ refl _
    with <-cmp (Singleton.x $ SemanticTime.day st₁) (Singleton.x $ SemanticTime.day st₂)
  ... | tri< a ¬b ¬c =
    yes (day< refl refl a)
  ... | tri> ¬a ¬b c = no λ x → contradiction (≤∧≢⇒< (dayLE x refl refl) ¬b) ¬a
  ... | tri≈ _ refl _
    with <-cmp (Singleton.x $ SemanticTime.hour st₁) (Singleton.x $ SemanticTime.hour st₂)
  ... | tri< a ¬b ¬c = yes (hour< refl refl refl a)
  ... | tri> ¬a ¬b c = no λ x → contradiction (≤∧≢⇒< (hourLE x refl refl refl) ¬b) ¬a
  ... | tri≈ _ refl _
    with <-cmp (Singleton.x $ SemanticTime.min st₁) (Singleton.x $ SemanticTime.min st₂)
  ... | tri< a ¬b ¬c =
    yes (min< refl refl refl refl a)
  ... | tri> ¬a ¬b c =
    no λ x → contradiction (≤∧≢⇒< (minLE x refl refl refl refl) ¬b) ¬a
  ... | tri≈ _ refl _
    with <-cmp (Singleton.x $ SemanticTime.sec st₁) (Singleton.x $ SemanticTime.sec st₂)
  ... | tri< a ¬b ¬c = yes (sec< refl refl refl refl refl a)
  ... | tri> ¬a ¬b c = no λ x → contradiction (≤∧≢⇒< (secLE x refl refl refl refl refl) ¬b) ¬a
  ... | tri≈ _ refl _ = yes (eq (mkSemanticTimeEq refl refl refl refl refl refl))

  -- `decidable` and `total` implies LE is a total order
  total
    : ∀ {@0 bs₁ bs₂ bs₃} {t₁ : Generic.Time bs₁} {t₂ : Generic.Time bs₂} {t₃ : Generic.Time bs₃}
     → (st₁ : SemanticTime t₁) (st₂ : SemanticTime t₂)
     → ¬ LE st₁ st₂ → LE st₂ st₁
  total st₁ st₂ ¬le
    with <-cmp (Singleton.x $ SemanticTime.year st₁) (Singleton.x $ SemanticTime.year st₂)
  ... | tri< a ¬b ¬c = contradiction (year< a) ¬le
  ... | tri> ¬a ¬b c = year< c
  ... | tri≈ _ refl _
    with <-cmp (Singleton.x $ SemanticTime.month st₁) (Singleton.x $ SemanticTime.month st₂)
  ... | tri< a ¬b ¬c = contradiction (month< refl a) ¬le
  ... | tri> ¬a ¬b c = month< refl c
  ... | tri≈ _ refl _
    with <-cmp (Singleton.x $ SemanticTime.day st₁) (Singleton.x $ SemanticTime.day st₂)
  ... | tri< a ¬b ¬c = contradiction (day< refl refl a) ¬le
  ... | tri> ¬a ¬b c = day< refl refl c
  ... | tri≈ _ refl _
    with <-cmp (Singleton.x $ SemanticTime.hour st₁) (Singleton.x $ SemanticTime.hour st₂)
  ... | tri< a ¬b ¬c = contradiction (hour< refl refl refl a) ¬le
  ... | tri> ¬a ¬b c = hour< refl refl refl c
  ... | tri≈ _ refl _
    with <-cmp (Singleton.x $ SemanticTime.min st₁) (Singleton.x $ SemanticTime.min st₂)
  ... | tri< a ¬b ¬c = contradiction (min< refl refl refl refl a) ¬le
  ... | tri> ¬a ¬b c = min< refl refl refl refl c
  ... | tri≈ _ refl _
    with <-cmp (Singleton.x $ SemanticTime.sec st₁) (Singleton.x $ SemanticTime.sec st₂)
  ... | tri< a ¬b ¬c = contradiction (sec< refl refl refl refl refl a) ¬le
  ... | tri> ¬a ¬b c = sec< refl refl refl refl refl c
  ... | tri≈ _ refl _ = eq (mkSemanticTimeEq refl refl refl refl refl refl)
