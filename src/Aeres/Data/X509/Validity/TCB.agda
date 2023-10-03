{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER
open import Aeres.Prelude

module Aeres.Data.X509.Validity.TCB where

record ValidityFields (@0 bs : List UInt8) : Set where
  constructor mkValidityFields
  field
    @0 {nb na} : List UInt8
    start : Time nb
    end : Time na
    @0 bs≡  : bs ≡ nb ++ na

Validity : @0 List UInt8 → Set
Validity xs = TLV Tag.Sequence ValidityFields xs

getStartTime getEndTime : ∀ {@0 bs} → Validity bs → Exists─ (List UInt8) Time

getStartTime v = _ , (ValidityFields.start ∘ TLV.val $ v)

getEndTime   v = _ , (ValidityFields.end ∘ TLV.val $ v)

-- TODO use windowing from RFC 5820
getYearNB : ∀ {@0 bs} → Validity bs →  ℕ
getYearNB (mkTLV len (mkValidityFields start end bs≡₁) len≡ bs≡) = Time.getYear start
getMonthNB : ∀ {@0 bs} → Validity bs →  ℕ
getMonthNB (mkTLV len (mkValidityFields start end bs≡₁) len≡ bs≡) = Time.getMonth start
getDayNB : ∀ {@0 bs} → Validity bs →  ℕ
getDayNB (mkTLV len (mkValidityFields start end bs≡₁) len≡ bs≡) = Time.getDay start
getHourNB : ∀ {@0 bs} → Validity bs →  ℕ
getHourNB (mkTLV len (mkValidityFields start end bs≡₁) len≡ bs≡) = Time.getHour start
getMinNB : ∀ {@0 bs} → Validity bs →  ℕ
getMinNB (mkTLV len (mkValidityFields start end bs≡₁) len≡ bs≡) = Time.getMin start
getSecNB : ∀ {@0 bs} → Validity bs →  ℕ
getSecNB (mkTLV len (mkValidityFields start end bs≡₁) len≡ bs≡) = Time.getSec start

getYearNA : ∀ {@0 bs} → Validity bs →  ℕ
getYearNA (mkTLV len (mkValidityFields start end bs≡₁) len≡ bs≡) = Time.getYear end
getMonthNA : ∀ {@0 bs} → Validity bs →  ℕ
getMonthNA (mkTLV len (mkValidityFields start end bs≡₁) len≡ bs≡) = Time.getMonth end
getDayNA : ∀ {@0 bs} → Validity bs →  ℕ
getDayNA (mkTLV len (mkValidityFields start end bs≡₁) len≡ bs≡) = Time.getDay end
getHourNA : ∀ {@0 bs} → Validity bs →  ℕ
getHourNA (mkTLV len (mkValidityFields start end bs≡₁) len≡ bs≡) = Time.getHour end
getMinNA : ∀ {@0 bs} → Validity bs →  ℕ
getMinNA (mkTLV len (mkValidityFields start end bs≡₁) len≡ bs≡) = Time.getMin end
getSecNA : ∀ {@0 bs} → Validity bs →  ℕ
getSecNA (mkTLV len (mkValidityFields start end bs≡₁) len≡ bs≡) = Time.getSec end
