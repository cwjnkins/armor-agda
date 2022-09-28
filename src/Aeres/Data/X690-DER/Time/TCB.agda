{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.TLV
open import Aeres.Data.X690-DER.Tag
open import Aeres.Prelude
import      Data.Nat.Properties as Nat

module Aeres.Data.X690-DER.Time.TCB where

open Base256

MonthRange : (mo₁ mo₂ : UInt8) → Set
MonthRange mo₁ mo₂ =   mo₁ ≡ # '0' × InRange '0' '9' mo₂
                     ⊎ mo₁ ≡ # '1' × InRange '0' '2' mo₂

DayRange : (d₁ d₂ : UInt8) → Set
DayRange d₁ d₂ =   InRange '0' '2' d₁ × InRange '0' '9' d₂
                 ⊎ toℕ d₁ ≡ toℕ '3' × InRange '0' '1' d₂

HourRange : (h₁ h₂ : UInt8) → Set
HourRange h₁ h₂ =    InRange '0' '1' h₁ × InRange '0' '9' h₂
                   ⊎ toℕ h₁ ≡ toℕ '2' × InRange '0' '3' h₂

MinuteRange : (mi₁ mi₂ : UInt8) → Set
MinuteRange mi₁ mi₂ = InRange '0' '5' mi₁ × InRange '0' '9' mi₂

SecRange : (s₁ s₂ : UInt8) → Set
SecRange s₁ s₂ = MinuteRange s₁ s₂ ⊎ (toℕ s₁ ≡ toℕ '6' × toℕ s₂ ≡ toℕ '0')

record MonthDayHourMinSecFields (@0 bs : List UInt8) : Set where
  constructor mkMDHMSFields
  field
    @0 {mo₁ mo₂ d₁ d₂ h₁ h₂ mi₁ mi₂ s₁ s₂} : UInt8

    mon : Singleton (asciiNum (mo₁ ∷ [ mo₂ ]))
    @0 monRange  : MonthRange mo₁ mo₂

    -- TODO: where do we check valid dom? (Feb, leap year, etc)
    day : Singleton (asciiNum (d₁ ∷ [ d₂ ]))
    @0 dayRange  : DayRange d₁ d₂

    hour : Singleton (asciiNum (h₁ ∷ [ h₂ ]))
    @0 hourRange : HourRange h₁ h₂

    min : Singleton (asciiNum (mi₁ ∷ [ mi₂ ]))
    @0 minRange : MinuteRange mi₁ mi₂

    sec : Singleton (asciiNum (s₁ ∷ [ s₂ ]))
    @0 secRange : SecRange s₁ s₂

    @0 bs≡ : bs ≡ mo₁ ∷ mo₂ ∷ d₁ ∷ d₂ ∷ h₁ ∷ h₂ ∷ mi₁ ∷ mi₂ ∷ s₁ ∷ [ s₂ ]

record UTCTimeFields (@0 bs : List UInt8) : Set where
  constructor mkUTCTimeFields
  field
    @0 {y1 y2 mn1 mn2 d1 d2 h1 h2 mi1 mi2 s1 s2 z} : UInt8

    year : Singleton (asciiNum (y1 ∷ [ y2 ]))
    @0 yearRange : All (InRange '0' '9') (y1 ∷ [ y2 ])

    mmddhhmmss : MonthDayHourMinSecFields (mn1 ∷ mn2 ∷ d1 ∷ d2 ∷ h1 ∷ h2 ∷ mi1 ∷ mi2 ∷ s1 ∷ [ s2 ])

    @0 term : z ≡ # toℕ 'Z'
    @0 bs≡  : bs ≡ y1 ∷ y2 ∷ mn1 ∷ mn2 ∷ d1 ∷ d2 ∷ h1 ∷ h2 ∷ mi1 ∷ mi2 ∷ s1 ∷ s2 ∷ [ z ]

UTCTime : (@0 _ : List UInt8) → Set
UTCTime xs = TLV Tag.UTCTime UTCTimeFields xs

record GenTimeFields (@0 bs : List UInt8) : Set where
  constructor mkGenTimeFields
  field
    @0 {y1 y2 y3 y4 z} : UInt8
    @0 {mdhms} : List UInt8

    year : Singleton (asciiNum (y1 ∷ y2 ∷ y3 ∷ [ y4 ]))
    @0 yearRange : All (InRange '0' '9') (y1 ∷ y2 ∷ y3 ∷ [ y4 ])

    mmddhhmmss : MonthDayHourMinSecFields mdhms

    @0 z≡ : z ≡ # 'Z'

    @0 bs≡ : bs ≡ y1 ∷ y2 ∷ y3 ∷ y4 ∷ mdhms ∷ʳ z

GenTime : (@0 _ : List UInt8) → Set
GenTime = TLV Tag.GeneralizedTime GenTimeFields

data Time : @0 List UInt8 → Set where
  utctm : ∀ {@0 bs} → UTCTime bs → Time bs
  gentm  : ∀ {@0 bs} → GenTime  bs → Time bs

getYear : ∀ {@0 bs} →  Time bs → ℕ
getYear (utctm x) = 
  let year = Singleton.x (UTCTimeFields.year (TLV.val x)) in
    case year <? 50 of λ where
      (yes _) → 2000 + year
      (no  _) → 1900 + year
getYear (gentm x) = Singleton.x (GenTimeFields.year (TLV.val x))

getMonth : ∀ {@0 bs} → Time bs → ℕ
getMonth (utctm x) = Singleton.x (MonthDayHourMinSecFields.mon (UTCTimeFields.mmddhhmmss (TLV.val x)))
getMonth (gentm x) = Singleton.x (MonthDayHourMinSecFields.mon (GenTimeFields.mmddhhmmss (TLV.val x)))

getDay : ∀ {@0 bs} → Time bs → ℕ
getDay (utctm x) = Singleton.x (MonthDayHourMinSecFields.day (UTCTimeFields.mmddhhmmss (TLV.val x)))
getDay (gentm x) = Singleton.x (MonthDayHourMinSecFields.day (GenTimeFields.mmddhhmmss (TLV.val x)))

getHour : ∀ {@0 bs} → Time bs → ℕ
getHour (utctm x) = Singleton.x (MonthDayHourMinSecFields.hour (UTCTimeFields.mmddhhmmss (TLV.val x)))
getHour (gentm x) = Singleton.x (MonthDayHourMinSecFields.hour (GenTimeFields.mmddhhmmss (TLV.val x)))

getMin : ∀ {@0 bs} → Time bs → ℕ
getMin (utctm x) = Singleton.x (MonthDayHourMinSecFields.min (UTCTimeFields.mmddhhmmss (TLV.val x)))
getMin (gentm x) = Singleton.x (MonthDayHourMinSecFields.min (GenTimeFields.mmddhhmmss (TLV.val x)))

getSec : ∀ {@0 bs} → Time bs → ℕ
getSec (utctm x) = Singleton.x (MonthDayHourMinSecFields.sec (UTCTimeFields.mmddhhmmss (TLV.val x)))
getSec (gentm x) = Singleton.x (MonthDayHourMinSecFields.sec (GenTimeFields.mmddhhmmss (TLV.val x)))

lessEq : ∀ {@0 bs₁ bs₂} → Time bs₁ → Time bs₂ → Bool
lessEq t₁ t₂
  with Nat.<-cmp (getYear t₁) (getYear t₂)
... | tri< _ _ _ = true
... | tri> _ _ _ = false
... | tri≈ _ _ _
  with Nat.<-cmp (getMonth t₁) (getMonth t₂)
... | tri< _ _ _ = true
... | tri> _ _ _ = false
... | tri≈ _ _ _
  with Nat.<-cmp (getDay t₁) (getDay t₂)
... | tri< _ _ _ = true
... | tri> _ _ _ = false
... | tri≈ _ _ _
  with Nat.<-cmp (getHour t₁) (getHour t₂)
... | tri< _ _ _ = true
... | tri> _ _ _ = false
... | tri≈ _ _ _
  with Nat.<-cmp (getMin t₁) (getMin t₂)
... | tri< _ _ _ = true
... | tri> _ _ _ = false
... | tri≈ _ _ _
  with Nat.<-cmp (getSec t₁) (getSec t₂)
... | tri< _ _ _ = true
... | tri> _ _ _ = false
... | tri≈ _ _ _ = true

--  with Base256.showFixed 2 (Foreign.Primitive.year u) = {!!}
--  just (mkGenTimeFields (singleton {!!} refl) {!!} {!!} {!!} {!!})
