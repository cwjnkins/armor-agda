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

module Aeres.Data.X690-DER.Time.GeneralizedTime.TCB where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Seq.TCB     UInt8

{- RFC 5820
-- 4.1.2.5.2.  GeneralizedTime
--
-- The generalized time type, GeneralizedTime, is a standard ASN.1 type
-- for variable precision representation of time.  Optionally, the
-- GeneralizedTime field can include a representation of the time
-- differential between local and Greenwich Mean Time.
--
-- For the purposes of this profile, GeneralizedTime values MUST be
-- expressed in Greenwich Mean Time (Zulu) and MUST include seconds
-- (i.e., times are YYYYMMDDHHMMSSZ), even where the number of seconds
-- is zero.  GeneralizedTime values MUST NOT include fractional seconds.
-}

record GeneralizedTimeFields (@0 bs : List UInt8) : Set where
  constructor mkGeneralizedTime
  field
    @0 {y m} : List UInt8
    year : Year₄ y
    mdhms : MDHMS m
    @0 bs≡ : bs ≡ y ++ m ++ [ # 'Z' ]

  getYear  = TimeType.getTime year
  getMonth = MDHMS.getMonth mdhms
  getDay   = MDHMS.getDay mdhms
  getHour  = MDHMS.getHour mdhms
  getSec   = MDHMS.getSec mdhms

GeneralizedTime : @0 List UInt8 → Set
GeneralizedTime = TLV Tag.GeneralizedTime GeneralizedTimeFields

GeneralizedTimeFieldsRep : @0 List UInt8 → Set
GeneralizedTimeFieldsRep = &ₚ Year₄ (&ₚ MDHMS (_≡ [ # 'Z' ]))

RawGeneralizedTimeFieldsRep : Raw GeneralizedTimeFieldsRep
RawGeneralizedTimeFieldsRep =
  Raw&ₚ RawYear₄ (Raw&ₚ RawMDHMS RawSubSingleton)

equivalent : Equivalent GeneralizedTimeFieldsRep GeneralizedTimeFields
proj₁ equivalent (mk&ₚ year (mk&ₚ mdhms refl refl) eq) = mkGeneralizedTime year mdhms eq
proj₂ equivalent (mkGeneralizedTime year mdhms bs≡) = mk&ₚ year (mk&ₚ mdhms refl refl) bs≡

RawGeneralizedTimeFields : Raw GeneralizedTimeFields
RawGeneralizedTimeFields = Iso.raw equivalent RawGeneralizedTimeFieldsRep

RawGeneralizedTime : Raw GeneralizedTime
RawGeneralizedTime = RawTLV _ RawGeneralizedTimeFields
