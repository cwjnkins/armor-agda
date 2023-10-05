{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Prelude
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Data.X690-DER.Time.MDHMS.TCB
  hiding (equivalent)
open import Aeres.Data.X690-DER.Time.TimeType.TCB
open import Aeres.Data.X690-DER.Time.Year.TCB
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Seq.TCB

module Aeres.Data.X690-DER.Time.UTCTime.TCB where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Seq.TCB     UInt8

record UTCTimeFields (@0 bs : List UInt8) : Set where
  constructor mkUTCTime
  field
    @0 {y m} : List UInt8
    year   : Year₂ y
    mdhms  : MDHMS m
    @0 bs≡ : bs ≡ y ++ m ++ [ # 'Z' ]

  getYear  : Window₂ → ℕ
  getYear w = TimeType.getTime (proj₂ (w year))

  getMonth  = MDHMS.getMonth mdhms
  getDay    = MDHMS.getDay mdhms
  getHour   = MDHMS.getHour mdhms
  getMinute = MDHMS.getMinute mdhms
  getSec    = MDHMS.getSec mdhms

UTCTime : @0 List UInt8 → Set
UTCTime = TLV Tag.UTCTime UTCTimeFields

UTCTimeFieldsRep : @0 List UInt8 → Set
UTCTimeFieldsRep = &ₚ Year₂ (&ₚ MDHMS (_≡ [ # 'Z' ]))

RawUTCTimeFieldsRep : Raw UTCTimeFieldsRep
RawUTCTimeFieldsRep =
   Raw&ₚ RawYear₂
  (Raw&ₚ RawMDHMS RawSubSingleton)

equivalent : Equivalent UTCTimeFieldsRep UTCTimeFields
proj₁ equivalent (mk&ₚ year (mk&ₚ mdhms refl refl) eq) = mkUTCTime year mdhms eq
proj₂ equivalent (mkUTCTime year mdhms bs≡) = mk&ₚ year (mk&ₚ mdhms refl refl) bs≡

RawUTCTimeFields : Raw UTCTimeFields
RawUTCTimeFields = Iso.raw equivalent RawUTCTimeFieldsRep

RawUTCTime : Raw UTCTime
RawUTCTime = RawTLV _ RawUTCTimeFields
