{-# OPTIONS --subtyping #-}

open import Aeres.Binary
import Aeres.Data.X690-DER.Time.Properties
import Aeres.Data.X690-DER.Time.TCB
import Aeres.Foreign.Time as Foreign
open import Aeres.Prelude

module Aeres.Data.X690-DER.Time where

open import Aeres.Data.X690-DER.Time.TCB
  public
  hiding (getYear ; getMonth ; getDay ; getHour ; getMin ; getSec ; lessEq ; module Time)

module Time where
  open Aeres.Data.X690-DER.Time.TCB
    public
    using (getYear ; getMonth ; getDay ; getHour ; getMin ; getSec ; lessEq)
  open Aeres.Data.X690-DER.Time.Properties
    public

  open import Aeres.Data.X690-DER.Length
  open import Aeres.Data.X690-DER.TLV
  import      Data.Nat.Properties as Nat

  fromFFI : (u : Foreign.UTCTime) → Maybe (Σ (List UInt8) Time)
  fromFFI u
    with Base256.showFixed 4 (Foreign.year u)
  ... | year@(y₁ ∷ y₂ ∷ y₃ ∷ y₄ ∷ [])
    with All.all? (inRange? '0' '9') (Vec.toList year)
  ... | no ¬p = nothing
  ... | yes yearRange
    with Base256.showFixed 2 (Foreign.month u)
  ... | month@(mo₁ ∷ mo₂ ∷ [])
    with MonthRange.monthRange? mo₁ mo₂
  ... | no _ = nothing
  ... | yes monthRange
    with Base256.showFixed 2 (Foreign.day u)
  ... | d₁ ∷ d₂ ∷ []
     with DayRange.dayRange? d₁ d₂
  ... | no _ = nothing
  ... | yes dayRange
    with Base256.showFixed 2 (Foreign.hour u)
  ... | h₁ ∷ h₂ ∷ []
    with HourRange.hourRange? h₁ h₂
  ... | no _ = nothing
  ... | yes hourRange
    with Base256.showFixed 2 (Foreign.minute u)
  ... | mi₁ ∷ mi₂ ∷ []
    with MinuteRange.minuteRange? mi₁ mi₂
  ... | no _ = nothing
  ... | yes minuteRange
    with Base256.showFixed 2 (Foreign.second u)
  ... | s₁ ∷ s₂ ∷ []
    with SecRange.secondRange? s₁ s₂
  ... | no _ = nothing
  ... | yes secRange =
    let
       bs : List UInt8
       bs = y₁ ∷ y₂ ∷ y₃ ∷ y₄ ∷ mo₁ ∷ mo₂ ∷ d₁ ∷ d₂ ∷ h₁ ∷ h₂ ∷ mi₁ ∷ mi₂ ∷ s₁ ∷ s₂ ∷ [ # 'Z' ]

       g : GenTimeFields bs
       g = (mkGenTimeFields self yearRange
              (mkMDHMSFields self monthRange self dayRange self hourRange self minuteRange self secRange refl)
              refl
              refl)

       <bs : length bs < 128
       <bs = Nat.≤-trans (s≤s (Lemmas.≡⇒≤ (GenTime.serialLength g))) (toWitness{Q = _ ≤? _} tt)

       u : Fin 128
       u = Fin.fromℕ< <bs

       l' : Length _
       l' = Length.toLength u

       l≡ : getLength l' ≡ length bs
       l≡ = (begin getLength l' ≡⟨ Length.getLength∘toLength-short u ⟩
                   toℕ u ≡⟨ Fin.toℕ-fromℕ< <bs ⟩
                   length bs ∎)
    in
    just (_ , gentm (mkTLV l' g l≡ refl))
    where open ≡-Reasoning
