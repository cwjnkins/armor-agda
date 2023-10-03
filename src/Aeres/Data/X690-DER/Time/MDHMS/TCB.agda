{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.Time.Day.TCB
open import Aeres.Data.X690-DER.Time.Hour.TCB
open import Aeres.Data.X690-DER.Time.Minute.TCB
open import Aeres.Data.X690-DER.Time.Month.TCB
open import Aeres.Data.X690-DER.Time.TimeType.TCB
open import Aeres.Data.X690-DER.Time.Sec.TCB
import      Aeres.Grammar.Definitions.Iso
import      Aeres.Grammar.Definitions.NonMalleable.Base
import      Aeres.Grammar.Parallel.TCB
import      Aeres.Grammar.Seq.TCB
open import Aeres.Prelude
open import Tactic.MonoidSolver
  using (solve ; solve-macro)

module Aeres.Data.X690-DER.Time.MDHMS.TCB where

open Aeres.Grammar.Definitions.Iso               UInt8
open Aeres.Grammar.Definitions.NonMalleable.Base UInt8
open Aeres.Grammar.Parallel.TCB                  UInt8
open Aeres.Grammar.Seq.TCB                       UInt8

record MDHMS (@0 bs : List UInt8) : Set where
  constructor mkMDHMS
  field
    @0 {mo d h mi s} : List UInt8
    month  : Month mo
    day    : Day d
    @0 dayRange : TimeType.getTime day ≤ daysInMonth month
    hour   : Hour h
    minute : Minute mi
    sec    : Sec s
    @0 bs≡ : bs ≡ mo ++ d ++ h ++ mi ++ s

  getMonth  = TimeType.getTime month
  getDay    = TimeType.getTime day
  getHour   = TimeType.getTime hour
  getMinute = TimeType.getTime minute
  getSec    = TimeType.getTime sec

MDHMSRep : @0 List UInt8 → Set
MDHMSRep = &ₚ (&ₚᵈ Month (λ mo → Σₚ Day λ _ day → Erased (TimeType.getTime day ≤ daysInMonth mo))) (&ₚ Hour (&ₚ Minute Sec))

equivalent : Equivalent MDHMSRep MDHMS
proj₁ equivalent (mk&ₚ (mk&ₚ{bs₁}{bs₂} mo d refl) (mk&ₚ h (mk&ₚ m s refl) refl) bs≡) =
  mkMDHMS mo (fstₚ d) (¡ (sndₚ d)) h m s (trans bs≡ (++-assoc bs₁ bs₂ _))
proj₂ equivalent (mkMDHMS{mo}{d}{h}{mi}{s} month day dayRange hour minute sec bs≡) =
  mk&ₚ (mk&ₚ month (mk×ₚ day (─ dayRange)) refl) (mk&ₚ hour (mk&ₚ minute sec refl) refl) (trans bs≡ (sym (++-assoc mo d _)))

RawDOM : Raw₁ RawMonth λ mo → Σₚ Day λ _ day → Erased (TimeType.getTime day ≤ daysInMonth mo)
Raw₁.D RawDOM  _ = ℕ
Raw₁.to RawDOM _ d = TimeType.getTime (fstₚ d)

RawMDHMSRep : Raw MDHMSRep
RawMDHMSRep =
   Raw&ₚ (Raw&ₚᵈ (RawTimeType _ _ _) RawDOM)
  (Raw&ₚ RawHour (Raw&ₚ RawMinute RawSec))

RawMDHMS : Raw MDHMS
RawMDHMS = Iso.raw equivalent RawMDHMSRep
